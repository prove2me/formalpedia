-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_zero_origin_value_and_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:20:24.198806+00:00
-- url     : https://prove2.me/submissions/2eb18812-3cad-4605-99e1-90fbebee4434

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

/-- Actual unbounded-variation scale primitive has both zero Laplace boundary terms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∫ t in (0 : ℝ)..(0 : ℝ), W t) = 0 ∧
      deriv (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) 0 = 0 := by
  have hzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hcont : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hzero
  have hI : IntervalIntegrable W volume (0 : ℝ) (0 : ℝ) :=
    IntervalIntegrable.refl
  have hd : HasDerivAt
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) (W 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right hI
      (hcont.stronglyMeasurableAtFilter volume (nhds (0 : ℝ))) hcont.continuousAt
  constructor
  · simp
  · rw [hd.deriv, hzero]
