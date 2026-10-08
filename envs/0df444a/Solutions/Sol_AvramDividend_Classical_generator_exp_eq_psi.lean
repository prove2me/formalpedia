-- Prove2me | solution 1 for AvramDividend.Classical.generator_exp_eq_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:28:53.900526+00:00
-- url     : https://prove2.me/submissions/0767066f-3d69-493f-bb5c-0022f35643ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ x : ℝ) :
    X.generator (fun z : ℝ => Real.exp (θ * z)) x =
      Real.exp (θ * x) * X.ψ θ := by
  have h1 : deriv (fun z : ℝ => Real.exp (θ * z)) x =
      θ * Real.exp (θ * x) := by
    have h := congrFun (iteratedDeriv_exp_const_mul 1 θ) x
    simpa using h
  have h2 : iteratedDeriv 2 (fun z : ℝ => Real.exp (θ * z)) x =
      θ ^ 2 * Real.exp (θ * x) := by
    have h := congrFun (iteratedDeriv_exp_const_mul 2 θ) x
    simpa using h
  have hJ :
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => Real.exp (θ * z)) x y ∂X.ν) =
        Real.exp (θ * x) *
          (∫ y in Iio (0 : ℝ),
            (Real.exp (θ * y) - 1 -
              θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂X.ν) := by
    simp_rw [generatorIntegrand_exp_mul θ x]
    rw [integral_const_mul]
  change
    X.σ ^ 2 / 2 *
        iteratedDeriv 2 (fun z : ℝ => Real.exp (θ * z)) x +
      X.c * deriv (fun z : ℝ => Real.exp (θ * z)) x +
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => Real.exp (θ * z)) x y ∂X.ν) =
      Real.exp (θ * x) *
        (X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
          (∫ y in Iio (0 : ℝ),
            (Real.exp (θ * y) - 1 -
              θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂X.ν))
  rw [h1, h2, hJ]
  ring
