-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_increment_exp_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:51:53.84768+00:00
-- url     : https://prove2.me/submissions/1f78654d-78fe-45b9-9453-f64c1e392e1f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.L2Space
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

/-- Exponential future increments after a bounded stopping time are L² random variables. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    MemLp (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) 2 P := by
  let g : Ω → ℝ := fun ω => Real.exp
    (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))
  change MemLp g 2 P
  have hint : Integrable g P := by
    apply Integrable.of_integral_ne_zero
    change (∫ ω, Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P) ≠ 0
    rw [levy_bounded_stopping_increment_laplace X τ hτ T hbounded h θ hθ]
    exact Real.exp_ne_zero _
  have hpow (ω : Ω) :
      g ω ^ 2 = Real.exp ((2 * θ) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω)) := by
    dsimp [g]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : Integrable (fun ω => g ω ^ 2) P := by
    apply Integrable.of_integral_ne_zero
    simp_rw [hpow]
    rw [levy_bounded_stopping_increment_laplace X τ hτ T hbounded h
      (2 * θ) (by linarith)]
    exact Real.exp_ne_zero _
  exact (memLp_two_iff_integrable_sq hint.1).2 hsq
