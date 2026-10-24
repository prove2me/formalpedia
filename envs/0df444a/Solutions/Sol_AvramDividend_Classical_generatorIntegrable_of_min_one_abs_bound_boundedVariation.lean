-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrable_of_min_one_abs_bound_boundedVariation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:32:07.636117+00:00
-- url     : https://prove2.me/submissions/ec7003e8-0a32-40f4-a9d8-27271b805a34

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_scalar_majorant_integrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- An integrable BV first-moment envelope controls the jump generator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (f : ℝ → ℝ) (x C : ℝ)
    (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand f x)
      (X.ν.restrict (Iio 0)))
    (hbound : ∀ y ∈ Iio (0 : ℝ),
      |SpectrallyNegativeLevy.generatorIntegrand f x y| ≤
        C * min 1 |y|) :
    X.GeneratorIntegrable f x := by
  have hdom : IntegrableOn (fun y : ℝ => C * min 1 |y|)
      (Iio (0 : ℝ)) X.ν :=
    chat07_bv_negative_jump_scalar_majorant_integrable X hBV C
  change Integrable (SpectrallyNegativeLevy.generatorIntegrand f x)
    (X.ν.restrict (Iio (0 : ℝ)))
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  simpa only [Real.norm_eq_abs] using hbound y hy
