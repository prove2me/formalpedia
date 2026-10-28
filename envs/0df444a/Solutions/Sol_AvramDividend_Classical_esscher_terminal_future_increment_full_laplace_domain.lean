-- Prove2me | solution 1 for AvramDividend.Classical.esscher_terminal_future_increment_full_laplace_domain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:25:59.913686+00:00
-- url     : https://prove2.me/submissions/48601fa7-d3a5-4e90-8d6d-c178f4b36d9d

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_future_increment_shifted_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_future_increment_negative_laplace
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The actual tilted Lévy increment Laplace exponent holds on its complete
real exponential-moment domain η ≥ -θ, including negative parameters. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ η : ℝ) (hθ : 0 ≤ θ) (hdomain : 0 ≤ θ + η)
    (s u T : ℝ≥0) (hT : s + u ≤ T) :
    (∫ ω, Real.exp (η * (X.X (s + u) ω - X.X s ω)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
      Real.exp ((u : ℝ) * (X.ψ (θ + η) - X.ψ θ)) := by
  rcases le_total 0 η with hη | hη
  · exact esscher_terminal_future_increment_shifted_laplace
      X θ η hθ hη s u T hT
  · have hε : 0 ≤ -η := neg_nonneg.mpr hη
    have hεθ : -η ≤ θ := by linarith [hdomain]
    simpa only [neg_neg, sub_neg_eq_add] using
      (esscher_terminal_future_increment_negative_laplace
        X θ (-η) hθ hε hεθ s u T hT)
