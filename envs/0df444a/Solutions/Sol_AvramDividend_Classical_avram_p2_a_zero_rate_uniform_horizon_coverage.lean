-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_horizon_coverage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:38:45.610022+00:00
-- url     : https://prove2.me/submissions/78fb6f0d-e057-4da5-81ec-51a0c421f0d1

import Mathlib
-- Full pinned Mathlib is needed for NNReal arithmetic and field_simp.

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- The original equal mesh has exactly the prescribed total NNReal duration. -/
theorem solution (T : ℝ≥0) (n : ℕ) :
    (((n : ℝ≥0) + 1) * (T / ((n : ℝ≥0) + 1))) = T := by
  have hn : ((n : ℝ≥0) + 1) ≠ 0 := by positivity
  field_simp
