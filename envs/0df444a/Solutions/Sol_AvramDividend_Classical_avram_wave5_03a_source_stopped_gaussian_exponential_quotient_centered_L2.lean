-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:12:16.041721+00:00
-- url     : https://prove2.me/submissions/d687f579-f11d-498e-a55a-b2ac3b79bd33

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_zero
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_centered_memLp_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The same original stopped source Gaussian difference quotient is centred and square-integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    MemLp (fun ω => (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) - 1) / θ) 2 P ∧
      (∫ ω, (Real.exp (θ *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ ∂P) = 0 := by
  classical
  have hbase :
      MemLp (fun ω => Real.exp (θ *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) 2 P := by
    convert (levy_bounded_stopping_compensated_increment_centered_memLp_two
      X τ hτ T hbounded h θ hθ) using 1
    funext ω
    congr 1
    rw [sub_eq_add_neg, Real.exp_add, mul_comm]
  constructor
  · have hscaled := hbase.const_mul θ⁻¹
    convert hscaled using 1
    funext ω
    ring
  · have hmean :=
      levy_bounded_stopping_compensated_increment_mean_zero
        X τ hτ T hbounded h θ hθ
    have hfun :
        (fun ω => (Real.exp (θ *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ) =
        (fun ω => (Real.exp (θ *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) * θ⁻¹) := by
      funext ω
      ring
    rw [hfun, integral_mul_const, hmean, zero_mul]
