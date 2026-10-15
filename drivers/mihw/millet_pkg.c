#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/skbuff.h>
#include <linux/file.h>
#include <linux/netfilter.h>
#include <linux/netfilter_ipv4.h>
#include <linux/netfilter_ipv6.h>
#include <linux/spinlock.h>
#include <linux/rbtree.h>
#include <linux/ktime.h>
#include <linux/time.h>
#include <linux/list.h>
#include <linux/types.h>
#include <net/sock.h>
#include <net/ip.h>
#include <net/tcp.h>
#include <net/inet_hashtables.h>
#include <net/inet6_hashtables.h>
#include "millet.h"


#define MAX_REC_UID 64
static struct pkg_uid_entry {
	uid_t uid;
	u64 generation;
	bool pending;
} uid_rec[MAX_REC_UID];
static DEFINE_SPINLOCK(uid_rec_lock);

int pkg_stat_show(struct seq_file *m, void *v)
{
	int i;
	unsigned long flags;
	uid_t uids[MAX_REC_UID];

	spin_lock_irqsave(&uid_rec_lock, flags);
	for (i = 0; i < MAX_REC_UID; i++)
		uids[i] = uid_rec[i].uid;
	spin_unlock_irqrestore(&uid_rec_lock, flags);
	for (i = 0; i < MAX_REC_UID; i++)
		if (uids[i])
			seq_printf(m, "%d\t", uids[i]);
	seq_printf(m, "\n");

	return 0;
}

static void pkg_add_uid(uid_t uid)
{
	int i, j;
	unsigned long flags;

	if (!uid)
		return;

	spin_lock_irqsave(&uid_rec_lock, flags);
	for (i = 0, j = MAX_REC_UID; i < MAX_REC_UID; i++) {
		if (!uid_rec[i].uid && j == MAX_REC_UID)
			j = i;
		else if (uid_rec[i].uid == uid) {
			/* Re-arm an entry whose previous notification is in flight. */
			if (uid_rec[i].pending) {
				uid_rec[i].generation++;
				uid_rec[i].pending = false;
			}
			goto out;
		}
	}

	if (j < MAX_REC_UID) {
		uid_rec[j].generation++;
		uid_rec[j].uid = uid;
		uid_rec[j].pending = false;
	} else {
		pr_err("%s : add uid:%d failed (full)!\n", __func__, uid);
	}

out:
	spin_unlock_irqrestore(&uid_rec_lock, flags);
}

static int pkg_sendmsg(struct task_struct *tsk,
		struct millet_data *data, struct millet_sock *sk)
{
	int ret = RET_OK;

	if (!sk || !data || !tsk) {
		pr_err("%s input invalid\n", __FUNCTION__);
		return RET_ERR;
	}

	data->msg_type = MSG_TO_USER;
	data->owner = PKG_TYPE;
	data->uid = data->mod.k_priv.pkg.pkg_owner;
	ret = millet_sendto_user(tsk, data, sk);

	return ret;
}

static void pkg_del_uid(uid_t uid)
{
	int i;
	unsigned long flags;

	spin_lock_irqsave(&uid_rec_lock, flags);
	for (i = 0; i < MAX_REC_UID; i++) {
		if (uid_rec[i].uid == uid) {
			uid_rec[i].generation++;
			uid_rec[i].uid = 0;
			uid_rec[i].pending = false;
			break;
		}
	}
	spin_unlock_irqrestore(&uid_rec_lock, flags);
}

static void pkg_clear_all(void)
{
	int i;
	unsigned long flags;

	spin_lock_irqsave(&uid_rec_lock, flags);
	for (i = 0; i < MAX_REC_UID; i++) {
		uid_rec[i].generation++;
		uid_rec[i].uid = 0;
		uid_rec[i].pending = false;
	}
	spin_unlock_irqrestore(&uid_rec_lock, flags);
}

static int pkg_claim_uid(uid_t uid, u64 *generation)
{
	int i, slot = -1;
	unsigned long flags;

	spin_lock_irqsave(&uid_rec_lock, flags);
	for (i = 0; i < MAX_REC_UID; i++) {
		if (uid_rec[i].uid == uid) {
			if (!uid_rec[i].pending) {
				uid_rec[i].pending = true;
				*generation = uid_rec[i].generation;
				slot = i;
			}
			break;
		}
	}
	spin_unlock_irqrestore(&uid_rec_lock, flags);

	return slot;
}

static void pkg_complete_uid(int slot, uid_t uid, u64 generation, int ret)
{
	unsigned long flags;
	struct pkg_uid_entry *entry = &uid_rec[slot];

	spin_lock_irqsave(&uid_rec_lock, flags);
	/* ADD/DEL/CLEAR may have replaced the registration while sending. */
	if (entry->uid == uid && entry->generation == generation &&
	    entry->pending) {
		entry->pending = false;
		if (ret > 0)
			entry->uid = 0;
	}
	spin_unlock_irqrestore(&uid_rec_lock, flags);
}

static void pkg_recv_hook(void *data, unsigned int len)
{
	struct millet_userconf *payload = (struct millet_userconf *) data;

	switch (payload->mod.u_priv.pkg.cmd) {
	case ADD_UID:
		pkg_add_uid(payload->mod.u_priv.pkg.uid);
		break;
	case DEL_UID:
		pkg_del_uid(payload->mod.u_priv.pkg.uid);
		break;
	case CLEAR_ALL_UID:
		pkg_clear_all();
		break;
	default:
		break;
	}

	return;
}

static void pkg_init_millet(struct millet_sock *sk)
{
	if (sk)
		sk->mod[PKG_TYPE].monitor = PKG_TYPE;
}

static uid_t __sock_i_uid(struct sock *sk)
{
	uid_t uid;

	if (sk && sk->sk_socket) {
		uid = SOCK_INODE(sk->sk_socket)->i_uid.val;
		return uid;
	}

	return 0;
}

static unsigned int pkg_ip4_in(void *priv, struct sk_buff *skb,
		const struct nf_hook_state *state)
{
	struct sock *sk;
	struct millet_data data = { 0 };
	uid_t uid;
	u64 generation;
	int slot, ret;
	int protocol;

	protocol = ip_hdr(skb)->protocol;
	if (protocol != IPPROTO_TCP)
		return NF_ACCEPT;

	sk = skb_to_full_sk(skb);
	if (sk == NULL || !sk_fullsock(sk))
		return NF_ACCEPT;

	uid = __sock_i_uid(sk);
	if (uid < UID_MIN_VALUE)
		return NF_ACCEPT;

	slot = pkg_claim_uid(uid, &generation);
	if (slot < 0)
		return NF_ACCEPT;
	data.mod.k_priv.pkg.owner_pid = 0;
	data.mod.k_priv.pkg.pkg_owner = (int) uid;
	ret = millet_sendmsg(PKG_TYPE, current, &data);
	pkg_complete_uid(slot, uid, generation, ret);
	if (ret < 0)
		pr_err("%s : up report failed!\n", __func__);

	return NF_ACCEPT;
}

static unsigned int pkg_ip6_in(void *priv, struct sk_buff *skb,
		const struct nf_hook_state *state)
{
	struct sock *sk;
	struct millet_data data = { 0 };
	unsigned int thoff = 0;
	unsigned short frag_off = 0;
	int protohdr;
	uid_t uid;
	u64 generation;
	int slot, ret;

	protohdr = ipv6_find_hdr(skb, &thoff, -1, &frag_off, NULL);
	if (protohdr != IPPROTO_TCP)
		return NF_ACCEPT;

	sk = skb_to_full_sk(skb);
	if (sk == NULL || !sk_fullsock(sk))
		return NF_ACCEPT;

	uid = __sock_i_uid(sk);
	if (uid < UID_MIN_VALUE)
		return NF_ACCEPT;

	slot = pkg_claim_uid(uid, &generation);
	if (slot < 0)
		return NF_ACCEPT;

	data.mod.k_priv.pkg.owner_pid = 0;
	data.mod.k_priv.pkg.pkg_owner = (int) uid;
	ret = millet_sendmsg(PKG_TYPE, current, &data);
	pkg_complete_uid(slot, uid, generation, ret);
	if (ret < 0)
		pr_err("%s : up report failed!\n", __func__);

	return NF_ACCEPT;
}

static inline unsigned int pkg_ip4_out(void *priv, struct sk_buff *skb,
		const struct nf_hook_state *state)
{
	return NF_ACCEPT;
}

static inline unsigned int pkg_ip6_out(void *priv, struct sk_buff *skb,
		const struct nf_hook_state *state)
{
	return NF_ACCEPT;
}

static struct nf_hook_ops pkg_nf_ops[] = {

		{
				.hook        =    pkg_ip4_in,
				.pf        =    NFPROTO_IPV4,
				.hooknum    =    NF_INET_LOCAL_IN,
				.priority    =    NF_IP_PRI_SELINUX_LAST + 1,
		},
		{
				.hook   =    pkg_ip6_in,
				.pf        =    NFPROTO_IPV6,
				.hooknum    =    NF_INET_LOCAL_IN,
				.priority    =    NF_IP6_PRI_SELINUX_LAST + 1,
		},

		{
				.hook        =    pkg_ip4_out,
				.pf        =    NFPROTO_IPV4,
				.hooknum    =    NF_INET_LOCAL_OUT,
				.priority    =    NF_IP_PRI_SELINUX_LAST + 1,
		},
		{
				.hook        =    pkg_ip6_out,
				.pf        =    NFPROTO_IPV6,
				.hooknum    =    NF_INET_LOCAL_OUT,
				.priority    =    NF_IP6_PRI_SELINUX_LAST + 1,
		},

};

static int __init millet_pkg_init(void)
{
	int ret;
	struct net *net = &init_net;

	pkg_clear_all();

	ret = nf_register_net_hooks(net, pkg_nf_ops, ARRAY_SIZE(pkg_nf_ops));
	if (ret < 0) {
		pr_err("nf_register_hooks(millet hooks) error\n");
		return RET_ERR;
	}
	pr_err("nf_register_hooks(millet hooks) success\n");
	register_millet_hook(PKG_TYPE, pkg_recv_hook, pkg_sendmsg,
			pkg_init_millet);
	return RET_OK;
}

static void __exit millet_pkg_exit(void)
{
	struct net *net = &init_net;

	unregister_millet_hook(PKG_TYPE);
	nf_unregister_net_hooks(net, pkg_nf_ops, ARRAY_SIZE(pkg_nf_ops));
}


module_init(millet_pkg_init);
module_exit(millet_pkg_exit);

MODULE_LICENSE("GPL");
