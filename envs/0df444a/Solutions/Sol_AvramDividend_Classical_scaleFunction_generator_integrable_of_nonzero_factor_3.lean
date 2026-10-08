-- Prove2me | solution 3 for AvramDividend.Classical.scaleFunction_generator_integrable_of_nonzero_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:04:50.269991+00:00
-- url     : https://prove2.me/submissions/0c170e71-e5f7-407e-87b8-ac16ca525b5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_levyMeasure_absolutelyContinuous_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_vcstar_contDiff_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x := by
  intro x hx
  rcases h_smooth with hσ | hbv | hvc
  · have hC2 : ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) :=
      (scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ).mono
        (by intro z hz; exact hz.1)
    exact scaleFunction_generatorIntegrable_of_contDiff_two
      X q W hW (cstar W).toReal x hx hC2
  · have hac : X.ν ≪ volume :=
      levyMeasure_absolutelyContinuous_of_standing_boundedVariation X hX hbv
    have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
      scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
        X hX q hq W hW hbv hac
    exact scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
      X q W hW hbv x hx.1 hC1
  · exact scaleFunction_generatorIntegrable_of_vcstar_contDiff_two
      X q W hW hvc hk x hx
