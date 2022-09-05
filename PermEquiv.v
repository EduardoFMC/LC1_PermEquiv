(** * Projeto de LC1 - 2022-1 (30 pontos)  *)

(**
  Projeto De Lógica Computacional 1. 2022/1
  Integrantes:
  
  1] Andrey Calaca Resende 180062433
  2]Gustavo Lopes Dezan 202033463
  3]Felipe Dantas Borges 202021749
  4]Eduardo Ferreira Marques Cavalcante 202006368
  
  Descrição: Projeto que formaliza a equivalência entre as diferentes noções de permutação denominadas perm e equiv
  utilizado o coq.
*)

Require Import PeanoNat List.
Open Scope nat_scope.
Require Import List Arith.
Require Import Permutation.
Open Scope nat_scope.

(** perm_hd = perm_skip acredito *)
(** perm_eq = perm_eq *)

(* Noção de permutação utilziado no trabalho, Permutation não tem perm_eq *)
Inductive perm : list nat -> list nat -> Prop :=
| perm_eq: forall l1, perm l1 l1
| perm_swap: forall x y l1, perm (x :: y :: l1) (y :: x :: l1)
| perm_hd: forall x l1 l2, perm l1 l2 -> perm (x :: l1) (x :: l2)
| perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

(** (2 pontos) *)
(** Mostrar que o Permutation do coq library possui equivalência com perm deste trabalho *)
Lemma perm_equiv_Permutation: forall l1 l2, perm l1 l2 <-> Permutation l1 l2.
Proof.
split.
  - intro H. induction H.
    -- apply Permutation_refl.
    -- apply Permutation.perm_swap.
    -- apply Permutation.perm_skip.
      --- apply IHperm.
    -- apply Permutation.perm_trans with (l2).
      --- apply IHperm1.
      --- apply IHperm2.
   - intro H. induction H.
     -- apply perm_eq.
     -- apply perm_hd.
       --- apply IHPermutation.
     -- apply perm_swap.
     -- apply perm_trans with (l').
       --- apply IHPermutation1.
       --- apply IHPermutation2.

Qed.

(* Fixpoint para definir número de ocorrencias de algum elemento em uma lista *)
Fixpoint num_oc (x: nat) (l: list nat): nat :=
  match l with
  | nil => 0
  | h::tl => if (x =? h) then S (num_oc x tl) else num_oc x tl
end.

(* Definição de equiv *)
Definition equiv l l' := forall n:nat, num_oc n l = num_oc n l'.

Lemma perm_app_cons: forall l1 l2 a, perm (a :: l1 ++ l2) (l1 ++ a :: l2).
Proof.
  induction l1.
  - intros l2 a.
    simpl.
    apply perm_eq.
  - intros l2 a2. (* porque o coq usa o 'a' como o numero natural?*)
    simpl.
    apply perm_trans with (a :: a2 :: l1 ++ l2).
    + apply perm_swap.
    + apply perm_hd.
      apply IHl1.
Qed.

Lemma num_oc_S: forall x l1 l2, num_oc x (l1 ++ x :: l2) = S (num_oc x (l1 ++ l2)).
Proof.
  induction l1.
  - intro l2.
    simpl.
    rewrite Nat.eqb_refl; reflexivity.
  - intro l2.
    simpl.
    destruct (x =? a); rewrite IHl1; reflexivity.
Qed.

Lemma num_occ_cons: forall l x n, num_oc x l = S n -> exists l1 l2, l = l1 ++ x :: l2 /\ num_oc x (l1 ++ l2) = n.
Proof.
  induction l.
  -intros.
    simpl in H.
    inversion H.
  -intros.
    simpl in H.
    destruct (x =? a) eqn: H1.
    +specialize (IHl x n).
      apply Nat.eqb_eq in H1.
      rewrite H1.
      exists nil.
      exists l.
      simpl.
      rewrite H1 in H.
      apply eq_add_S in H.
      split.
      *reflexivity.
      *assumption.
    +apply IHl in H.
      destruct H.
      destruct H.
      destruct H.
      rewrite H.
      exists (a :: x0).
      exists x1.
      split.
      *reflexivity.
      *simpl.
        rewrite H1.
        assumption.
      Qed.

Lemma num_oc_neq: forall n a l1 l2, n =? a = false -> num_oc n (l1 ++ a :: l2) = num_oc n (l1 ++ l2).
Proof.
  induction l1.
  - intros l2 H.
    simpl.
    rewrite H.
    reflexivity.
  - intros l2 Hfalse.
    simpl.
    destruct (n =? a0) eqn:H.
    + apply (IHl1 l2) in Hfalse.
      rewrite Hfalse; reflexivity.
    + apply (IHl1 l2) in Hfalse.
      assumption.
Qed.


Lemma equiv_nil: forall l, equiv nil l -> l = nil.
Proof.
  intro l.
  case l.
  - intro H.
    reflexivity.
  - intros n l' H. unfold equiv in H.
    specialize (H n). simpl in H.
    rewrite Nat.eqb_refl in H.
    inversion H.
Qed.


Lemma equiv_to_perm: forall l l', equiv l l' -> perm l l'.
Proof.
  induction l.
  - intros.
    apply equiv_nil in H.
    rewrite H.
    apply perm_eq.
       
  - intros.
    assert (H' := H).
    unfold equiv in H'.
    specialize (H' a).
    simpl in H'.
    rewrite Nat.eqb_refl in H'.
    symmetry in H'.
    apply num_occ_cons in H'.
    destruct H'. 
    destruct H0.
    destruct H0.
    assert(H2:=IHl).
    specialize (IHl (x++x0)).
    rewrite H0.
    apply (perm_trans (a :: l) (a :: x ++ x0) (x ++ a :: x0) ).
    -- apply perm_hd.
       apply IHl.
       rewrite H0 in H.
       intro.
       unfold equiv in H.
       specialize (H n).
       inversion H.
       destruct (n =? a) eqn: eq.
       --- apply Nat.eqb_eq in eq.
           rewrite eq in H4.
           rewrite (num_oc_S a x x0) in H4 .
           inversion H4.
           rewrite eq.
           auto.
       --- replace (num_oc n (x ++ a :: x0)) with (num_oc n (x ++ x0)) in H4.
           ---- auto.
           ---- symmetry.
                apply (num_oc_neq n a x x0 ).
                auto.
    -- apply perm_app_cons.
    
Qed.

(** (18 pontos) *)
(* Prova do equiv <-> perm *)
Theorem perm_equiv: forall l l', equiv l l' <-> perm l l'.
Proof.
  intros l l'.
  split.
  - apply equiv_to_perm. (* equiv -> perm dificil de se provar sem lemas separados *)
  
  - intro H. induction H.
    -- unfold equiv. 
       intro x. 
       reflexivity.
    -- unfold equiv in *. intro n. simpl. destruct (n =? x) eqn: H. 
       + destruct (n =? y) eqn: H'.
       --- reflexivity.
       --- reflexivity.
       + destruct (n =? y) eqn: H'.
       --- reflexivity.
       --- reflexivity.
    -- unfold equiv in *.
       intro n.
       destruct (n=?x) eqn:H'.
       --- simpl. rewrite H'. rewrite IHperm. reflexivity.
       --- simpl. rewrite H'. rewrite IHperm. reflexivity.
    -- unfold equiv in *.
       intro n.
       specialize (IHperm1 n).
       rewrite IHperm1.
       apply IHperm2.

Qed.
