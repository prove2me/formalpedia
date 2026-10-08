-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_compact_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:49:09.589975+00:00
-- url     : https://prove2.me/submissions/a35ebd83-275d-4bea-86bd-4d1480bb1486

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_compact_prod_integrable

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
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    [SFinite (X.ν.restrict (Iio 0))] :
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
  exact MeasureTheory.integral_prod _
    (scaleFunction_generatorIntegrand_compact_prod_integrable
      X q W hW a l u hl hlu hu hC2 μ)
