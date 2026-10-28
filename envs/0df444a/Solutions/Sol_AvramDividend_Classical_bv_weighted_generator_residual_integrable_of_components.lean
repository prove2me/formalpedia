-- Prove2me | solution 1 for AvramDividend.Classical.bv_weighted_generator_residual_integrable_of_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:55:53.871097+00:00
-- url     : https://prove2.me/submissions/02e27355-0527-4e58-a911-0c09298c18cf

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_eq_drift_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The BV generator residual inherits integrability from its three weighted components. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q θ : ℝ) (W : ℝ → ℝ)
    (hDint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hJint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
      (Ioi (0 : ℝ)))
    (hWint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ))) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * (X.generator W x - q * W x))
      (Ioi (0 : ℝ)) := by
  have hpoint (x : ℝ) :
      Real.exp (-(θ * x)) * (X.generator W x - q * W x) =
      X.c * (Real.exp (-(θ * x)) * deriv W x) +
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
        q * (Real.exp (-(θ * x)) * W x) := by
    rw [boundedVariation_generator_eq_drift_integral X hbv W x]
    change Real.exp (-(θ * x)) *
      (X.c * deriv W x +
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
        q * W x) = _
    ring
  have hfun :
      (fun x : ℝ =>
        Real.exp (-(θ * x)) * (X.generator W x - q * W x)) =
      (fun x : ℝ =>
        X.c * (Real.exp (-(θ * x)) * deriv W x) +
          Real.exp (-(θ * x)) *
            (∫ y in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
          q * (Real.exp (-(θ * x)) * W x)) :=
    funext hpoint
  rw [hfun]
  exact ((hDint.const_mul X.c).add hJint).sub (hWint.const_mul q)
