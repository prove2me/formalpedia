-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_compensated_exp_mixed_time_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:52:15.240542+00:00
-- url     : https://prove2.me/submissions/a0580622-a09f-428a-a270-bfe2eebb5651

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_exp_mixed_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- The two-parameter compensated stopped exponential moment factors across horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h k : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    ∫ ω, Real.exp (θ *
      (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω) -
      ((h + k) : ℝ) * X.ψ θ) *
      Real.exp (η *
        (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω) -
        ((h + k) : ℝ) * X.ψ η) ∂P =
        Real.exp ((h : ℝ) * (X.ψ (θ + η) - X.ψ θ - X.ψ η)) *
          Real.exp ((k : ℝ) * (X.ψ (θ + η) - X.ψ θ - X.ψ η)) := by
  simp only [← NNReal.coe_add]
  rw [levy_bounded_stopping_compensated_exp_mixed_moment
    X τ hτ T hbounded (h + k) θ η hθ hη]
  rw [← Real.exp_add]
  congr 1
  simp only [NNReal.coe_add, add_mul]
