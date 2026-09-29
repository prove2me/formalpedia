-- Prove2me | solution 1 for FamousTheorems.card_general_linear_group_finite_field_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:54:38.818446+00:00
-- url     : https://prove2.me/submissions/402e2d15-0e14-49bc-a265-18e022d56227

import Mathlib

theorem solution {F : Type*} [Field F] [Fintype F] (n : ℕ) :
    Nat.card (GL (Fin n) F) = ∏ i : Fin n, (Fintype.card F ^ n - Fintype.card F ^ (i : ℕ)) :=
  Matrix.card_GL_field n
