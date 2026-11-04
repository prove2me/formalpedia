-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_predecessor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:29:38.565549+00:00
-- url     : https://prove2.me/submissions/fce1c96f-5ab0-4c24-8811-cf7eb6c279ee

import Mathlib
-- Keep full pinned Mathlib for NNReal, Real notation and truncated subtraction.

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- Truncated nonnegative-time subtraction recovers the exact predecessor
of each uniform original-source grid cell. -/
theorem solution (j : ℕ) (δ : ℝ≥0) :
    (((j + 1 : ℕ) : ℝ≥0) * δ) - δ = (j : ℝ≥0) * δ := by
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_tsub_cancel_right]
