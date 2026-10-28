-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_discounted_increment_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:08:04.178259+00:00
-- url     : https://prove2.me/submissions/d8e2f9a1-0703-45ab-a088-563aad3a2ea7

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

/-- A discounted exponential of the post-stopping Lévy increment has an explicit second moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) ^ 2 ∂P =
        Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * q)) := by
  have hpow (ω : Ω) :
      (Real.exp (-(q * (h : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) ^ 2 =
      Real.exp ((2 * θ) * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        2 * (q * (h : ℝ))) := by
    rw [← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpow, Real.exp_sub, div_eq_mul_inv]
  rw [integral_mul_const]
  rw [levy_bounded_stopping_increment_laplace X τ hτ T hbounded h
    (2 * θ) (by linarith)]
  rw [← div_eq_mul_inv, ← Real.exp_sub]
  congr 1
  ring
