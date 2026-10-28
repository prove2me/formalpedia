-- Prove2me | solution 1 for AvramDividend.Classical.chat01_levy_exponential_early_event_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:45:21.854564+00:00
-- url     : https://prove2.me/submissions/c5268d12-628c-4a10-9767-09d78b0f699f

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal

/-- At two deterministic times, the compensated Lévy exponential
    has equal integrals over every event measurable at the earlier time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A) :
    (∫ w in A, Real.exp (θ * X.X s w -
      (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) =
    (∫ w in A, Real.exp (θ * X.X t w -
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) := by
  exact (levy_compensated_exponential_martingale X θ hθ).setIntegral_eq hst hA
