-- Prove2me | solution 1 for FamousTheorems.jacobson_noether_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:49:27.84986+00:00
-- url     : https://prove2.me/submissions/418a98fa-1a7f-4229-9d59-b21a8ab0857b

import Mathlib

theorem solution (D : Type*) [DivisionRing D] [Algebra.IsAlgebraic (Subring.center D) D] (h : Subring.center D ≠ ⊤) :
    ∃ x ∉ Subring.center D, IsSeparable (Subring.center D) x :=
  JacobsonNoether.exists_separable_and_not_isCentral D h
