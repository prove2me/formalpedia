-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_uniform_real_rate_mesh_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:10:52.507352+00:00
-- url     : https://prove2.me/submissions/500a1e11-3dba-4bfe-813d-d10bb65deeef

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_width_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Real nonnegative cell rates sum exactly to C times the original horizon. -/
theorem solution (T : ℝ≥0) (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    (∑ _i ∈ Finset.range (n + 1),
      ENNReal.ofReal (C * ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ))) =
        ENNReal.ofReal (C * (T : ℝ)) := by
  have hsum :
      (∑ _i ∈ Finset.range (n + 1),
        ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)) = (T : ℝ≥0∞) := by
    exact_mod_cast avram_p2_34dbea70_uniform_original_grid_width_sum T n
  simp_rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_coe_nnreal]
  rw [← Finset.mul_sum, hsum]
