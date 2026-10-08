-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_compact_fubini_of_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:39:29.441993+00:00
-- url     : https://prove2.me/submissions/7e658310-99d6-473a-8c11-a964f6daa16e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_compact_fubini
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

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
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫ p : ℝ × ℝ,
      (Icc l u ×ˢ Iio (0 : ℝ)).indicator
        (fun z : ℝ × ℝ =>
          SpectrallyNegativeLevy.generatorIntegrand W z.1 z.2) p
       ∂(μ.prod (X.ν.restrict (Iio 0)))) =
    ∫ x : ℝ, ∫ y : ℝ,
      (Icc l u ×ˢ Iio (0 : ℝ)).indicator
        (fun z : ℝ × ℝ =>
          SpectrallyNegativeLevy.generatorIntegrand W z.1 z.2) (x,y)
      ∂(X.ν.restrict (Iio 0)) ∂μ := by
  letI : SFinite (X.ν.restrict (Iio 0)) :=
    levy_negative_jump_measure_sFinite X
  exact scaleFunction_generatorIntegrand_compact_fubini
    X q W hW a l u hl hlu hu hC2 μ
