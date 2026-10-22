-- Prove2me | solution 1 for AvramDividend.Classical.chat03_nonnegative_min_truncation_gap_le_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:00:02.692163+00:00
-- url     : https://prove2.me/submissions/9694b519-d0f0-4fd4-927e-93de3f19bcd9

import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_quadratic_tail_pointwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-!
The real truncation error is nonnegative and bounded by the second
moment divided by the positive truncation threshold.
-/
theorem solution (R y : ℝ) (hR : 0 < R) (hy : 0 ≤ y) :
    0 ≤ y - min y R ∧ y - min y R ≤ y ^ 2 / R := by
  constructor
  · exact sub_nonneg.mpr (min_le_left y R)
  · by_cases h : R ≤ y
    · rw [min_eq_right h]
      have ht := chat03_nonnegative_quadratic_tail_pointwise R y hR hy
      simp only [if_pos h] at ht
      exact (sub_le_self y (le_of_lt hR)).trans ht
    · rw [min_eq_left (le_of_lt (lt_of_not_ge h))]
      simpa using div_nonneg (sq_nonneg y) (le_of_lt hR)
