-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB314_gaussian_density_inverse_volatility_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:55:26.305244+00:00
-- url     : https://prove2.me/submissions/0e091ed2-1698-403e-b0a9-d6327d337795

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

/-- Original Gaussian normalisation commutes with inverse volatility. -/
theorem solution (sigma y : ℝ) :
    (Real.sqrt (2 * Real.pi))⁻¹ * sigma⁻¹ * y =
      (1 / (sigma * Real.sqrt (2 * Real.pi))) * y := by
  simp only [one_div, mul_inv_rev]
