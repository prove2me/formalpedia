-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_ennreal_truncated_clock_toNNReal_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:16:16.760953+00:00
-- url     : https://prove2.me/submissions/2f80ee6a-ea5a-4a46-a3a8-7024c2b329ad

import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-- A horizon-truncated extended nonnegative stopping time is finite
and its NNReal projection stays below that horizon. -/
theorem solution (a : ℝ≥0∞) (T : ℝ≥0) :
    (min a (T : ℝ≥0∞)).toNNReal ≤ T := by
  have hle : min a (T : ℝ≥0∞) ≤ (T : ℝ≥0∞) :=
    min_le_right _ _
  have hfin : min a (T : ℝ≥0∞) ≠ ∞ := by
    exact ne_top_of_le_ne_top (by simp) hle
  exact (ENNReal.toNNReal_le_toNNReal hfin (by simp)).2 hle
