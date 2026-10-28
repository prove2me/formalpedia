-- Prove2me | solution 1 for AvramDividend.Classical.bv_weighted_generator_residual_integral_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:18:16.675323+00:00
-- url     : https://prove2.me/submissions/4747e144-3c3f-4f66-b679-1b3bd3a6392d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_eq_drift_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The BV generator residual's weighted integral splits into drift, jump and q-scale terms. -/
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
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
    (hLaplace : (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * W x) = (X.ψ θ - q)⁻¹) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) =
      X.c * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * deriv W x) +
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) -
      q * (X.ψ θ - q)⁻¹ := by
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
  have hD : IntegrableOn (fun x : ℝ =>
      X.c * (Real.exp (-(θ * x)) * deriv W x))
      (Ioi (0 : ℝ)) := hDint.const_mul X.c
  have hWq : IntegrableOn (fun x : ℝ =>
      q * (Real.exp (-(θ * x)) * W x))
      (Ioi (0 : ℝ)) := hWint.const_mul q
  calc
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) =
      (∫ x in Ioi (0 : ℝ),
        X.c * (Real.exp (-(θ * x)) * deriv W x) +
          Real.exp (-(θ * x)) *
            (∫ y in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
          q * (Real.exp (-(θ * x)) * W x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact hpoint x
    _ = X.c * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * deriv W x) +
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) -
      q * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * W x) := by
      have hsub :
          (∫ x in Ioi (0 : ℝ),
            X.c * (Real.exp (-(θ * x)) * deriv W x) +
              Real.exp (-(θ * x)) *
                (∫ y in Iio (0 : ℝ),
                  SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
              q * (Real.exp (-(θ * x)) * W x)) =
          (∫ x in Ioi (0 : ℝ),
            X.c * (Real.exp (-(θ * x)) * deriv W x) +
              Real.exp (-(θ * x)) *
                (∫ y in Iio (0 : ℝ),
                  SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) -
          (∫ x in Ioi (0 : ℝ),
            q * (Real.exp (-(θ * x)) * W x)) := by
        simpa only [Pi.add_apply] using
          (integral_sub (hD.add hJint) hWq)
      rw [hsub, integral_add hD hJint,
        integral_const_mul, integral_const_mul]
    _ = _ := by rw [hLaplace]
