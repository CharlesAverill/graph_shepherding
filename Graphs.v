Require Import Coq.Setoids.Setoid.

Definition graph : Type := {V : Type & V -> V -> bool}.

Definition create : forall V, (V -> V -> bool) -> graph := @existT _ _.

Definition vertices : graph -> Type := @projT1 _ _.

Definition adjacent : forall g1, vertices g1 -> vertices g1 -> bool := @projT2 _ _.

Definition complement : graph -> graph := fun g1 => create (vertices g1) (fun v1 v2 => negb (adjacent g1 v1 v2)).

Definition injective : forall {t1 t2}, (t1 -> t2) -> Prop := fun t1 t2 f1 => forall x1 x2, f1 x1 = f1 x2 -> x1 = x2.

Definition surjective : forall {t1 t2}, (t1 -> t2) -> Prop := fun t1 t2 f1 => forall x1, exists x2, f1 x2 = x1.

Definition bijective : forall {t1 t2}, (t1 -> t2) -> Prop := fun t1 t2 f1 => injective f1 /\ surjective f1.

Definition isomorphic : graph -> graph -> Prop := fun g1 g2 => exists f1, bijective f1 /\ (forall x1 x2, adjacent g1 x1 x2 = adjacent g2 (f1 x1) (f1 x2)).

Infix "~" := isomorphic (at level 70).

Theorem C1 : forall b1 b2, negb b1 = negb b2 <-> b1 = b2.
Proof.
    intros. destruct b1, b2; split; intros; try reflexivity; try inversion H.
Qed.
