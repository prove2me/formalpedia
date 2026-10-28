-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_compensated_increment_exact_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:21:17.432589+00:00
-- url     : https://prove2.me/submissions/2ffab7c7-3ee9-4ebc-9bf8-f522c15bd9cb

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_one
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_second_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Exact variance of the cumulant-compensated Lévy exponential increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) - 1) ^ 2 ∂P =
        Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1 := by
  let f : Ω → ℝ := fun ω => Real.exp (θ *
    (X.X (τ ω + h) ω - X.X (τ ω) ω) -
    (h : ℝ) * X.ψ θ)
  change (∫ ω, (f ω - 1) ^ 2 ∂P) = _
  have hmean : (∫ ω, f ω ∂P) = 1 :=
    levy_bounded_stopping_compensated_increment_mean_one
      X τ hτ T hbounded h θ hθ
  have hm2 : (∫ ω, f ω ^ 2 ∂P) =
      Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) :=
    levy_bounded_stopping_compensated_increment_second_moment
      X τ hτ T hbounded h θ hθ
  have hf : Integrable f P := by
    apply Integrable.of_integral_ne_zero
    rw [hmean]
    norm_num
  have hf2 : Integrable (fun ω => f ω ^ 2) P := by
    apply Integrable.of_integral_ne_zero
    rw [hm2]
    exact Real.exp_ne_zero _
  have htwo : Integrable (fun ω => (2 : ℝ) * f ω) P :=
    hf.const_mul 2
  have hminus : Integrable (fun ω => f ω ^ 2 - 2 * f ω) P :=
    hf2.sub htwo
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
  have hconst : (∫ _ : Ω, (1 : ℝ) ∂P) = 1 := by simp
  calc
    (∫ ω, (f ω - 1) ^ 2 ∂P) =
        ∫ ω, (f ω ^ 2 - 2 * f ω + 1) ∂P := by
          congr 1
          ext ω
          ring
    _ = (∫ ω, f ω ^ 2 ∂P) -
        (∫ ω, 2 * f ω ∂P) + (∫ _ : Ω, (1 : ℝ) ∂P) := by
          rw [integral_add hminus hone]
          rw [integral_sub hf2 htwo]
    _ = Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1 := by
          rw [hm2, integral_const_mul, hmean, hconst]
          ring
