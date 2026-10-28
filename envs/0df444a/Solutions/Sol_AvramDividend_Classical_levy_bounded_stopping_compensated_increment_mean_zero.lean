-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_compensated_increment_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:17:24.272582+00:00
-- url     : https://prove2.me/submissions/d6f33981-d962-4795-9861-465ec6fcbc10

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- The cumulant-compensated exponential increment is centred under a probability law. -/
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
      (h : ℝ) * X.ψ θ) - 1) ∂P = 0 := by
  have hmean := levy_bounded_stopping_compensated_increment_mean_one
    X τ hτ T hbounded h θ hθ
  have hint : Integrable (fun ω => Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ)) P := by
    apply Integrable.of_integral_ne_zero
    rw [hmean]
    norm_num
  rw [integral_sub hint (integrable_const (1 : ℝ))]
  rw [hmean]
  simp
