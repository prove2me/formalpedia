-- Prove2me | solution 1 for FamousTheorems.cantor_set_ternary_digits_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:57:44.009725+00:00
-- url     : https://prove2.me/submissions/0c9d1384-bc2a-42c4-813e-3ae27800e0b9

import Mathlib

theorem solution : cantorSet = {x : ℝ | ∃ a : ℕ → Fin 3, (∀ i, a i ≠ 1) ∧ Real.ofDigits a = x} :=
  cantorSet_eq_zero_two_ofDigits
