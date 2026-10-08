-- Prove2me | solution 1 for Combinatorics.finite_symmetric_local_lemma_avoidance_positive
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:42:26.477179+00:00
-- url     : https://prove2.me/submissions/2f63662a-f3eb-4691-8ff7-1185249f69bc

import Theorems.Thm_Combinatorics_finite_symmetric_local_lemma_avoidance_card_bound
import Mathlib

theorem solution
    (Omega I : Type*) [Fintype Omega] [Nonempty Omega] [DecidableEq Omega]
    [Fintype I] [DecidableEq I]
    (A : I -> Finset Omega) (dep : I -> I -> Prop) [DecidableRel dep]
    (x : Real) (hx0 : 0 <= x) (hx1 : x < 1)
    (hprob : forall i,
      ((A i).card : Real) / (Fintype.card Omega : Real) <=
        x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card)
    (hindependent : forall (i : I) (S : Finset I),
      (forall j, Membership.mem S j -> Not (dep i j)) ->
      ((Finset.filter (fun w => Membership.mem (A i) w)
          (Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w)))).card : Real) /
          (Fintype.card Omega : Real) =
        (((Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w))).card : Real) /
            (Fintype.card Omega : Real)) *
          ((A i).card : Real) / (Fintype.card Omega : Real)) :
    forall S : Finset I,
      0 < (Finset.univ.filter (fun w : Omega =>
        forall j, Membership.mem S j -> Not (Membership.mem (A j) w))).card := by
  intro S
  have hbound := Combinatorics.finite_symmetric_local_lemma_avoidance_card_bound
    Omega I A dep x hx0 hx1 hprob hindependent S
  have hfactor : 0 < (1 - x) ^ S.card := pow_pos (by linarith) _
  have hOmega : 0 < (Fintype.card Omega : Real) := by positivity
  have hcount : 0 <
      ((Finset.univ.filter (fun w : Omega =>
        forall j, Membership.mem S j -> Not (Membership.mem (A j) w))).card : Real) :=
    lt_of_lt_of_le (mul_pos hfactor hOmega) hbound
  exact_mod_cast hcount
