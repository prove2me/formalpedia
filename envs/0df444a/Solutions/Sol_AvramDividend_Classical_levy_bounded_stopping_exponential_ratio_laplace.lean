-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_exponential_ratio_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:08:07.680117+00:00
-- url     : https://prove2.me/submissions/7a1391db-7499-4534-b7da-95c6655e1838

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- The expectation of a future-to-stopped surplus exponential ratio has the Lévy Laplace factor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ * X.X (τ ω + h) ω) /
      Real.exp (θ * X.X (τ ω) ω) ∂P =
        Real.exp ((h : ℝ) * X.ψ θ) := by
  have hratio (ω : Ω) :
      Real.exp (θ * X.X (τ ω + h) ω) /
        Real.exp (θ * X.X (τ ω) ω) =
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  simp_rw [hratio]
  exact levy_bounded_stopping_increment_laplace
    X τ hτ T hbounded h θ hθ
