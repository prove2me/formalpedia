-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_increment_exp_mixed_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:21:13.8014+00:00
-- url     : https://prove2.me/submissions/7c7d1e35-8edf-4038-a4b3-9dba18fa2f97

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

/-- Mixed exponential moments of a Lévy increment after bounded stopping. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    ∫ ω, Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω)) *
      Real.exp (η * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P =
        Real.exp ((h : ℝ) * X.ψ (θ + η)) := by
  have hprod (ω : Ω) :
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) *
        Real.exp (η * (X.X (τ ω + h) ω - X.X (τ ω) ω)) =
      Real.exp ((θ + η) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hprod]
  exact levy_bounded_stopping_increment_laplace
    X τ hτ T hbounded h (θ + η) (by linarith)
