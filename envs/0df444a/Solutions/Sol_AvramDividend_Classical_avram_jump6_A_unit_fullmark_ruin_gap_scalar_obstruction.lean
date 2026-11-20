-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_unit_fullmark_ruin_gap_scalar_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:01:24.311933+00:00
-- url     : https://prove2.me/submissions/b0ae132c-99ba-44f4-afba-c16e1955841a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
noncomputable section
theorem solution
    (y b t : ℝ)
    (hy0 : 0 ≤ y) (hycap : y ≤ 1 / 5)
    (hB : b ≤ 1 / 100) (ht : t ≤ 1 / 10) :
    (if y - 2 < 0 then 0 else 1 + (y - 2) + (y - 2) ^ 2) = (0 : ℝ) ∧
    (1 + y + y ^ 2) + b - 2 + 2 * t ≤ -(11 / 20 : ℝ) := by
  have hy2 : y - 2 < 0 := by linarith
  have hsq : y ^ 2 ≤ (1 / 25 : ℝ) := by
    nlinarith [mul_nonneg
      (show 0 ≤ (1 / 5 : ℝ) - y by linarith)
      (show 0 ≤ (1 / 5 : ℝ) + y by linarith)]
  constructor
  · simp [hy2]
  · nlinarith
