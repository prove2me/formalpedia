-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_compensated_variance_time_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:57:08.777831+00:00
-- url     : https://prove2.me/submissions/efd40d74-9171-4978-b562-361c3590f0ba

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_exact_variance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Exact second-moment semigroup formula for centred stopped Lévy exponentials. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h k : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (θ *
      (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω) -
      ((h + k) : ℝ) * X.ψ θ) - 1) ^ 2 ∂P =
      (Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1) +
        (Real.exp ((k : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1) +
        (Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1) * (Real.exp ((k : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1) := by
  simp only [← NNReal.coe_add]
  rw [levy_bounded_stopping_compensated_increment_exact_variance
    X τ hτ T hbounded (h + k) θ hθ]
  simp only [NNReal.coe_add, add_mul, Real.exp_add]
  ring
