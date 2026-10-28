-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_compensated_increment_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:07:28.107599+00:00
-- url     : https://prove2.me/submissions/89c8b07f-54ef-4295-a2f3-7f1297f49993

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Exact second moment of the cumulant-compensated Lévy increment after bounded stopping. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ)) ^ 2 ∂P =
        Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) := by
  have hpow (ω : Ω) :
      (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ)) ^ 2 =
      Real.exp ((2 * θ) * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        2 * ((h : ℝ) * X.ψ θ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpow, Real.exp_sub, div_eq_mul_inv]
  rw [integral_mul_const]
  rw [levy_bounded_stopping_increment_laplace X τ hτ T hbounded h
    (2 * θ) (by linarith)]
  rw [← div_eq_mul_inv, ← Real.exp_sub]
  congr 1
  ring
