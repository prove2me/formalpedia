-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_uniform_ennreal_rate_mesh_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:10:57.205328+00:00
-- url     : https://prove2.me/submissions/0c5de1b8-7309-4a41-aa81-5f6e0ef68e10

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_width_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact extended-nonnegative grid total for a constant cell-rate bound. -/
theorem solution (T C : ℝ≥0) (n : ℕ) :
    (∑ _i ∈ Finset.range (n + 1),
      ((C * (T / ((n : ℝ≥0) + 1)) : ℝ≥0) : ℝ≥0∞)) =
        ((C * T : ℝ≥0) : ℝ≥0∞) := by
  have hnn :
      (∑ _i ∈ Finset.range (n + 1),
        C * (T / ((n : ℝ≥0) + 1))) = C * T := by
    rw [← Finset.mul_sum,
      avram_p2_34dbea70_uniform_original_grid_width_sum]
  exact_mod_cast hnn
