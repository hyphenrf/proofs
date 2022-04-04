(** Lemmas:
      1) (m * k) divides n -> m divides n
      2) pq|r = p(q|r) unless r = true, p = false
    with Lemmas 1 and 2, we can prove that this is correct:
      p := n mod 4   = 0
      q := n mod 100 = 0
      r := n mod 400 = 0
      pq|r = p(q|r)
      by showing that r = true, p = false is impossible.
*)

(* auxillary stuff *)
Definition divides m n := exists k, n = m * k.
Infix "divides" := divides (at level 40).

Goal 400 <> 0 /\ 4 <> 0 /\ 100 <> 0. repeat split; discriminate. Qed.

Goal forall n m,
	m <> 0 -> Nat.modulo n m = 0 <-> m divides n.
Proof.
	Require Import PeanoNat.
	apply Nat.mod_divides.
Qed.

(* 1 *)

Require Import Mult.
Lemma mul_mod: forall k m n,
	(m * k) divides n -> m divides n.
Proof.
	intros k m n H.
	destruct H.
	exists (k * x).
	rewrite H.
	apply mult_assoc_reverse.
Qed.


(* 2 *)

Goal forall r p : Prop, (r -> p) -> ~(r /\ ~p).
tauto. Qed.

Lemma pqr: forall p q r: Prop,
	(r -> p) -> p /\ q \/ r <-> p /\ (q \/ r).
tauto. Qed.


(* The actual proof *)

Theorem leap: forall y,
	let p := 4 divides y   in
	let q := 100 divides y in
	let r := 400 divides y in
	p /\ ~q \/ r <-> p /\ (~q \/ r).
Proof.
	intro y.
	apply pqr.
	replace 400 with (4 * 100) by reflexivity.
	apply mul_mod.
Qed.
