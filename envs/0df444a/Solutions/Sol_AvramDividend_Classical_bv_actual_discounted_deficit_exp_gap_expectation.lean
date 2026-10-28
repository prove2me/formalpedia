-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_discounted_deficit_exp_gap_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:22:29.513913+00:00
-- url     : https://prove2.me/submissions/b87cb405-9096-40e9-82e8-7279dd9db914

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The expected exponential drift-deficit gap has the exact Levy transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ ω, (1 : ℝ) -
        Real.exp (θ * X.X t ω) *
          Real.exp (-((t : ℝ) * X.drift * θ)) ∂P) =
      1 - Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hθ0 : 0 ≤ θ := by linarith
  have hExp : Integrable
      (fun ω => Real.exp (θ * X.X t ω) *
        Real.exp (-((t : ℝ) * X.drift * θ))) P := by
    exact ((X.laplace t θ hθ0).1).mul_const _
  rw [integral_sub (integrable_const (1 : ℝ)) hExp]
  rw [bv_actual_levy_drift_normalised_laplace X hBV t θ hθ]
  simp
