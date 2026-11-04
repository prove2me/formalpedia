-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_uniform_original_grid_adjacent_duration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:50:44.884068+00:00
-- url     : https://prove2.me/submissions/03b94b7f-46d3-465e-bdb0-cbda5fe65e80

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- Each successive interval of the uniform source-time grid has exactly
the prescribed half-open cell width, with NNReal truncated subtraction. -/
theorem solution (T : ℝ≥0) (n i : ℕ) :
    (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
      (i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) =
    T / ((n : ℝ≥0) + 1) := by
  have hstep :
      (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) =
      (i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) +
        T / ((n : ℝ≥0) + 1) := by
    push_cast
    ring
  rw [hstep]
  simp
