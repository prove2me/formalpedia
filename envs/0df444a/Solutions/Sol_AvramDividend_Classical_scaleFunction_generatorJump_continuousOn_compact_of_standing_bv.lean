-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorJump_continuousOn_compact_of_standing_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:34:42.88299+00:00
-- url     : https://prove2.me/submissions/ad809ef6-6789-4e78-ab9c-adabdba28e8d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorJump_continuousOn_compact_of_ae_continuity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by
  exact scaleFunction_generatorJump_continuousOn_compact_of_ae_continuity
    X q W hW a l u hl hlu hu hC2
    (scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv
      X hX hbv q W hW a l u hl hlu hu hC2)
