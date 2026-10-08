-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_smooth_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:24:55.74021+00:00
-- url     : https://prove2.me/submissions/e35a2f24-a781-40fc-954f-bf1dfe53c14f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})) :
    DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  by_cases hBV : X.BoundedVariation
  · exact (hw_smooth.2 hBV).differentiableOn (by norm_num)
  · exact (hw_smooth.1 hBV).differentiableOn (by norm_num)
