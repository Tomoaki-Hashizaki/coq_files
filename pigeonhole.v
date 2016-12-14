Require Import List.
Require Import ClassicalFacts.
Require Import PeanoNat.
Require Import Omega.

Lemma Sn_le_Sm__n_le_m :
  forall {n m :nat}, S n <= S m -> n <= m.
Proof.
  intros n m.
  omega.
Qed.

Theorem contradiction_implies_anything : forall (P Q : Prop),
  (P /\ ~P) -> Q.
Proof.
  intros p q contra.
  inversion contra as [HP HNP].
  unfold not in HNP.
  apply HNP in HP.
  contradiction.
Qed.

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X),
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X xs.
  induction xs.
  (* basis *)
    intros.
    right.
    apply H.
  (* induction step *)
    intros.
    inversion H.
    (* x = a *)
      left.
      apply ai_here.
    (* b = a *)
      apply IHxs in H1.
      inversion H1.
      (* appears_in x xs *)
        left.
        apply ai_later.
        apply H3.
      (* appears_in x ys *)
        right.
        apply H3.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X),
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs.
  induction xs.
  (* basis *)
    intros.
    inversion H.
    (* appears_in x nil *)
      inversion H0.
    (* appears_in x ys *)
      simpl.
      apply H0.
  (* induction step *)
    intros.
    (* appears_in x (a :: xs) *)
      inversion H.
      (* x = a *)
        inversion H0.
        rewrite <- app_comm_cons.
        apply ai_here.
      (* b = a *)
        rewrite <- app_comm_cons.
        apply ai_later.
        apply IHxs.
        left.
        apply H2.
    (* appears_in x ys *)
      rewrite <- app_comm_cons.
      apply ai_later.
      apply IHxs.
      right.
      apply H0.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l ->
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction l.
  (* basis *)
    inversion H.
  (* induction step *)
    inversion H.
    (* x = a *)
      exists nil.
      exists l.
      simpl.
      reflexivity.
    (* b = a *)
      apply IHl in H1.
      destruct H1.
      destruct H1.
      exists (a :: x0).
      exists x1.
      simpl.
      rewrite <- H1.
      reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
| rep_here : forall x l, appears_in x l -> repeats (x :: l)
| rep_later : forall x l, repeats l -> repeats (x :: l).

Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X),
  excluded_middle ->
  (forall x, appears_in x l1 -> appears_in x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros X l1.
  induction l1 as [|x l1']; intros.
  (* basis *)
    inversion H1.
  (* induction step *)
    destruct (H (appears_in x l1')).
    (* appears_in x l1' *)
      apply rep_here.
      apply H2.
    (* ~ appears_in x l1' *)
      apply rep_later.
      destruct (H (appears_in x l2)).
      (* appears_in x l1' *)
        apply appears_in_app_split in H3.
        inversion H3.
        inversion H4.
        apply IHl1' with (l2:=(x0 ++ x1)).
        apply H.
        intros.
        destruct (H (x2 = x)).
        (* x2 = x *)
          subst.
          contradiction.
        (* x2 <> x *)
          apply ai_later with (b:=x) in H6.
          apply H0 in H6.
          rewrite H5 in H6.
          apply appears_in_app in H6.
          apply app_appears_in.
          destruct H6.
          (* appears_in x2 x0 *)
            left.
            apply H6.
          (* appears_in x2 (x :: x1) *)
            right.
            inversion H6.
            (* x2 = x *)
              contradiction.
            (* b = x *)
              assumption.
              rewrite H5 in H1.
              rewrite app_length in H1.
              simpl in H1.
              rewrite <- plus_n_Sm in H1.
              apply Sn_le_Sm__n_le_m in H1.
              unfold lt.
              rewrite app_length.
              apply H1.
              apply contradiction_implies_anything with (P:=(appears_in x l2)).
              split.
              apply H0.
              apply ai_here.
              apply H3.
Qed.