-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_increment_exp_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:48:37.442431+00:00
-- url     : https://prove2.me/submissions/a26b09e8-b08c-4919-8499-573e8b24f51a

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

/-- The squared exponential of a post-stopping Lévy increment has an explicit second moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω))) ^ 2 ∂P =
        Real.exp ((h : ℝ) * X.ψ (2 * θ)) := by
  have hpow (ω : Ω) :
      (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) ^ 2 =
        Real.exp ((2 * θ) *
          (X.X (τ ω + h) ω - X.X (τ ω) ω)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpow]
  exact levy_bounded_stopping_increment_laplace X τ hτ T hbounded h
    (2 * θ) (by linarith)
