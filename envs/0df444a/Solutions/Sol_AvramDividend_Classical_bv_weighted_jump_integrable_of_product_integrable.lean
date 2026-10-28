-- Prove2me | solution 1 for AvramDividend.Classical.bv_weighted_jump_integrable_of_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:56:42.387014+00:00
-- url     : https://prove2.me/submissions/c645aa50-8f8c-470f-8444-216706949d8e

import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Fubini's partial-integrability statement for the weighted generator jump term. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (W : ℝ → ℝ)
    (hprod : Integrable
      (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
      (Ioi (0 : ℝ)) := by
  haveI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  have hleft := hprod.integral_prod_left
  change Integrable (fun x : ℝ =>
    Real.exp (-(θ * x)) *
      (∫ y,
        SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio (0 : ℝ)))))
    (volume.restrict (Ioi (0 : ℝ)))
  simpa only [integral_const_mul] using hleft
