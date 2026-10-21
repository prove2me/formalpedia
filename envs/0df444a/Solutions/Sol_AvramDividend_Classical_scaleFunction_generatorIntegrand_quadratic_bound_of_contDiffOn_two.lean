-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_quadratic_bound_of_contDiffOn_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:50:51.076933+00:00
-- url     : https://prove2.me/submissions/590cd933-afe4-49f7-abfb-2c54fdc2bcfe

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_aestronglyMeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
The generator integrand of the scale function is quadratic at the origin and
almost-everywhere strongly measurable.

The quadratic bound is the Proved theorem
`scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two`, and the
almost-everywhere strong measurability is the Proved theorem
`scaleFunction_generatorIntegrand_aestronglyMeasurable`; this theorem
conjoins the two.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ C : ℝ, 0 ≤ C ∧
      AEStronglyMeasurable
        (SpectrallyNegativeLevy.generatorIntegrand W x)
        (X.ν.restrict (Iio 0)) ∧
      ∀ y ∈ Iio (0 : ℝ),
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          C * min 1 (y ^ 2) := by
  obtain ⟨C, hC, hbound⟩ :=
    scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two
      X q W hW a x hx hC2
  refine ⟨C, hC, ?_, ?_⟩
  · exact scaleFunction_generatorIntegrand_aestronglyMeasurable X q W hW x
  · intro y hy
    exact hbound y hy
