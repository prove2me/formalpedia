-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB301_original_gaussian_good_bad_mesh_constant_assembly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:40:02.081361+00:00
-- url     : https://prove2.me/submissions/4c885716-a68e-479b-9909-2963f61fade9

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

/-- Localised bad variation and Gaussian good-cell constants fit the finite-cap mesh envelope. -/
theorem solution (sigma : ℝ) (hsigma : 0 < sigma)
    (n M m : ℕ) (hm : 0 < m) :
    ENNReal.ofReal ((M : ℝ) / (m : ℝ)) +
      (Real.toNNReal ((2 * (n : ℝ)) /
        (sigma * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
        (m : ℝ≥0∞)⁻¹ ≤
      (Real.toNNReal (1 + (M : ℝ) +
        (2 * (n : ℝ)) / (sigma * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
        (m : ℝ≥0∞)⁻¹ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let A : ℝ := (2 * (n : ℝ)) / (sigma * Real.sqrt (2 * Real.pi))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ 1 + (M : ℝ) + A := by positivity
  have hbad : ENNReal.ofReal ((M : ℝ) / (m : ℝ)) =
      (M : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hmR]
    norm_cast
  have hNN : (M : ℝ≥0) + Real.toNNReal A ≤
      Real.toNNReal (1 + (M : ℝ) + A) := by
    apply NNReal.coe_le_coe.mpr
    change ((M : ℝ) + (Real.toNNReal A : ℝ)) ≤
      (Real.toNNReal (1 + (M : ℝ) + A) : ℝ)
    rw [Real.coe_toNNReal _ hA, Real.coe_toNNReal _ hC]
    linarith
  have hCE : (M : ℝ≥0∞) + (Real.toNNReal A : ℝ≥0∞) ≤
      (Real.toNNReal (1 + (M : ℝ) + A) : ℝ≥0∞) := by
    exact_mod_cast hNN
  change ENNReal.ofReal ((M : ℝ) / (m : ℝ)) +
      (Real.toNNReal A : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ ≤
    (Real.toNNReal (1 + (M : ℝ) + A) : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹
  calc
    _ = ((M : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹) +
        (Real.toNNReal A : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ := by
          rw [hbad]
    _ = ((M : ℝ≥0∞) + (Real.toNNReal A : ℝ≥0∞)) *
          (m : ℝ≥0∞)⁻¹ := by rw [add_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hCE (by positivity)
