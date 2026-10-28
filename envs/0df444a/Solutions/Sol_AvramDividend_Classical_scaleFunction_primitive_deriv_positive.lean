-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_primitive_deriv_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:19:14.128501+00:00
-- url     : https://prove2.me/submissions/150de105-46c9-40a2-be29-6439b830cf8f

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set intervalIntegral
open scoped NNReal ENNReal

/-- The scale-function primitive is differentiable at every positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x →
      deriv (fun t : ℝ => ∫ z in (0 : ℝ)..t, W z) x = W x := by
  intro x hx
  have hint : IntervalIntegrable W volume (0 : ℝ) x :=
    scaleFunction_intervalIntegrable_nonnegative X q W hW 0 x (le_refl 0) (le_of_lt hx)
  have hcont : ContinuousAt W x :=
    scaleFunction_continuousAt_away_zero X q W hW x (ne_of_gt hx)
  have hmeas : StronglyMeasurableAtFilter W (nhds x) volume :=
    (chat04_scaleFunction_measurable_of_punctured_continuity X q W hW).aestronglyMeasurable.stronglyMeasurableAtFilter
  exact (integral_hasDerivAt_right hint hmeas hcont).deriv
