-- Prove2me | solution 1 for AvramDividend.Classical.bv_small_negative_first_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:30:52.230623+00:00
-- url     : https://prove2.me/submissions/952561f1-3687-40b0-a0f4-8158e6e3769c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set
open scoped ENNReal NNReal

open MeasureTheory Filter Set NNReal ENNReal AvramDividend.Classical in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => -y) (Ioo (-1 : ℝ) 0) X.ν := by
  refine ⟨(measurable_id.neg).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa [Real.norm_eq_abs, abs_neg] using hBV.2
