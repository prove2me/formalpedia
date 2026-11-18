-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB124_original_unit_horizon_mesh_step_eventually_below_overshoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:30:37.008243+00:00
-- url     : https://prove2.me/submissions/e5b6334a-bedd-4021-8c4a-ea8af964819d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section
/-- The original physical unit-horizon mesh eventually fits inside the extra tube. -/
theorem solution (m : ℕ) (hm : 15999 ≤ m) :
    (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0) ≤
      (1 / 16000 : ℝ≥0) := by
  have hden : (16000 : ℝ≥0) ≤ ((m + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast (show 16000 ≤ m + 1 by omega)
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ≥0) < 16000) hden
