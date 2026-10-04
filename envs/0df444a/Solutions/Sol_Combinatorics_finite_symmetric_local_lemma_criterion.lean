-- Prove2me | solution 1 for Combinatorics.finite_symmetric_local_lemma_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:26:53.548162+00:00
-- url     : https://prove2.me/submissions/b51434dc-0259-4251-9e08-83d5ad432efb

import Theorems.Thm_Combinatorics_finite_symmetric_local_lemma_avoidance_positive
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
            Not (Membership.mem (A j) w)))).card : Real) / (Fintype.card Omega : Real) =
        (((Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w))).card : Real) / (Fintype.card Omega : Real)) *
          ((A i).card : Real) / (Fintype.card Omega : Real)) :
    Exists fun w : Omega => forall i, Not (Membership.mem (A i) w) := by
  classical
  have hpos := Combinatorics.finite_symmetric_local_lemma_avoidance_positive
    Omega I A dep x hx0 hx1 hprob hindependent Finset.univ
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  refine ⟨w, ?_⟩
  intro i
  exact (Finset.mem_filter.mp hw).2 i (Finset.mem_univ i)
