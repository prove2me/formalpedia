-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB183_uniform_physical_grid_step_fits_centered_long_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:16:01.595019+00:00
-- url     : https://prove2.me/submissions/a2c0bc0b-059c-4ecd-81d1-9d24c0f8bbf6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
noncomputable section
/-- Physical uniform grid overshoot remains inside long centered Brownian tube. -/
theorem solution
    (n m : ℕ) (hm : 16000 * n ≤ m + 1) :
    (1 / 1000 : ℝ≥0) +
      (n : ℝ≥0) / ((m : ℝ≥0) + 1) ≤
      (17 / 16000 : ℝ≥0) := by
  have hd : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmR : (16000 : ℝ) * (n : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast hm
  have hDiv : (n : ℝ) / ((m : ℝ) + 1) ≤ (1 / 16000 : ℝ) := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have hR : (1 / 1000 : ℝ) +
      (n : ℝ) / ((m : ℝ) + 1) ≤ (17 / 16000 : ℝ) := by
    linarith
  exact_mod_cast hR
