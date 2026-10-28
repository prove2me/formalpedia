-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_generator_q_harmonic_all_barriers_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:01:42.311257+00:00
-- url     : https://prove2.me/submissions/a0d52f88-820a-4fc8-a852-1639817c1047

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_laplace_family
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a : ℝ) (ha : 0 < a) :
    ∀ y ∈ Ioo 0 a,
      X.GeneratorIntegrable W y ∧ X.generator W y - q * W y = 0 := by
  have hC1 := scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hBV
  exact scaleFunction_generator_interval_harmonic_of_laplace_family X hX q hq W hW a ha
    (generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero X hX hBV hBV.1 q W hW hC1)
    (bv_weighted_generator_residual_family_from_scale_20261026 X hX hBV q hq W hW)
    (fun x hx => scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one X q W hW hBV x hx.1 hC1)
