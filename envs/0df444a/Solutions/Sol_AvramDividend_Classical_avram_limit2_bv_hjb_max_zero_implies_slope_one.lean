-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_bv_hjb_max_zero_implies_slope_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:29:02.615352+00:00
-- url     : https://prove2.me/submissions/5446c1b6-ad4b-4bc2-8060-46fb99cc1236

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The original BV HJB maximum equality enforces the dividend slope bound
    required by original stopped cash to perpetual real value adapters. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y := by
  intro y hy hyC
  have hmax := (hw_hjb y hy hyC).2
  have hslope : 1 - deriv w y ≤ 0 :=
    le_trans (le_max_right _ _) (le_of_eq hmax)
  linarith
