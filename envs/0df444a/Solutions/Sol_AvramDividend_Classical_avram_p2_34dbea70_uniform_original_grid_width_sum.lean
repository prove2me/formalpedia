-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_uniform_original_grid_width_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:05:49.396017+00:00
-- url     : https://prove2.me/submissions/19fb31d9-77cc-4f6c-892a-14785c5219c7

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal BigOperators

/-- The exact uniform NNReal grid widths sum to the original horizon. -/
theorem solution (T : ℝ≥0) (n : ℕ) :
    (∑ _i ∈ Finset.range (n + 1), T / ((n : ℝ≥0) + 1)) = T := by
  have hden : ((n : ℝ≥0) + 1) ≠ 0 := by positivity
  calc
    (∑ _i ∈ Finset.range (n + 1), T / ((n : ℝ≥0) + 1)) =
        (n + 1) • (T / ((n : ℝ≥0) + 1)) := by simp
    _ = ((n : ℝ≥0) + 1) * (T / ((n : ℝ≥0) + 1)) := by
      rw [nsmul_eq_mul]
      norm_cast
    _ = T := by
      rw [mul_div_cancel₀ T hden]
