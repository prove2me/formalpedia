-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_integrable_of_nonzero_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:09:19.256295+00:00
-- url     : https://prove2.me/submissions/7a44d25d-3c46-4f7d-98a6-5f279c5af41e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_below_cstar_of_vcstar
import Theorems.Thm_AvramDividend_Classical_levyMeasure_absolutelyContinuous_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_absolutely_continuous_levy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

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
  · have hC2global :=
      scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
    have hC2 :
        ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) := by
      exact hC2global.mono (by
        intro z hz
        exact hz.1)
    exact
      scaleFunction_generatorIntegrable_of_contDiff_two
        X q W hW (cstar W).toReal x hx hC2
  · have hac :
        X.ν ≪ volume :=
      levyMeasure_absolutelyContinuous_of_standing_boundedVariation X hX hbv
    have hC1 :=
      scaleFunction_contDiff_one_of_absolutely_continuous_levy
        X hX q hq W hW hac
    exact
      scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
        X q W hW hbv x hx.1 hC1
  · have hC2 :=
      scaleFunction_contDiff_two_below_cstar_of_vcstar W hvc hk
    exact
      scaleFunction_generatorIntegrable_of_contDiff_two
        X q W hW (cstar W).toReal x hx hC2
