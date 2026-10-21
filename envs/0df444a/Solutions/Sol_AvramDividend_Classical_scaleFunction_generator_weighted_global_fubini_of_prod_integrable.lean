-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_weighted_global_fubini_of_prod_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:10:16.661928+00:00
-- url     : https://prove2.me/submissions/7a63c9e4-3cc6-4e68-8e5a-21ea7a8187b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
The discounted jump integral of the generator integrand of the scale function
may be integrated in the other order.

The integrability of the product integrand over the product of the two
restricted measures is the hypothesis; the swap itself is
`integral_integral_swap`, and the equality of the two iterated integrals is
the Fubini identity.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ : ℝ)
    (hprod : Integrable
      (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
    ∫ y in Iio (0 : ℝ),
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν := by
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  calc
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
    ∫ x in Ioi (0 : ℝ),
      (∫ y in Iio (0 : ℝ),
        Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [integral_const_mul]
    _ = ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν :=
          integral_integral_swap hprod
