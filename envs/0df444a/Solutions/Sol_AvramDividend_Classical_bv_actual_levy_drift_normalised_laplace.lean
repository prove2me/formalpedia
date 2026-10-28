-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_drift_normalised_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:38:08.610926+00:00
-- url     : https://prove2.me/submissions/441559eb-2cae-488f-8864-834ba06dfc9d

import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The drift-normalised one-time transform of the actual BV Levy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ ω, Real.exp (θ * X.X t ω) *
        Real.exp (-((t : ℝ) * X.drift * θ)) ∂P) =
      Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)) := by
  have hθ0 : 0 ≤ θ := le_trans (by norm_num) hθ
  have hlap := (X.laplace t θ hθ0).2
  change (∫ ω, Real.exp (θ * X.X t ω) ∂P) =
    Real.exp ((t : ℝ) * X.ψ θ) at hlap
  have hdef := bv_exponent_negative_jump_deficit_exact X hBV θ hθ
  have harg :
      (t : ℝ) * X.ψ θ + (-((t : ℝ) * X.drift * θ)) =
      -((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν) := by
    rw [← hdef]
    ring
  calc
    (∫ ω, Real.exp (θ * X.X t ω) *
        Real.exp (-((t : ℝ) * X.drift * θ)) ∂P) =
      (∫ ω, Real.exp (θ * X.X t ω) ∂P) *
        Real.exp (-((t : ℝ) * X.drift * θ)) := by
          rw [integral_mul_const]
    _ = Real.exp ((t : ℝ) * X.ψ θ) *
        Real.exp (-((t : ℝ) * X.drift * θ)) := by
          rw [hlap]
    _ = Real.exp (-((t : ℝ) *
          ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)) := by
          rw [← Real.exp_add, harg]
