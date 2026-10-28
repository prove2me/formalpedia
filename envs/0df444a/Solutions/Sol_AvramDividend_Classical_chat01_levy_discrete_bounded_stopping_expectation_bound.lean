-- Prove2me | solution 1 for AvramDividend.Classical.chat01_levy_discrete_bounded_stopping_expectation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:15:30.765396+00:00
-- url     : https://prove2.me/submissions/3b6c55e7-3813-4cdc-b16e-8bb7006196ba

import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat01_levy_exponential_nat_sampled_martingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal

/-- The expected compensated Lévy exponential at an earlier bounded
    discrete stopping time is at most its value at a later one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun (n : ℕ) => 𝓕 (e n)
         mono' := by
           intro i j hij
           exact 𝓕.mono (he hij)
         le' := by
           intro n
           exact 𝓕.le (e n) } : Filtration ℕ mΩ))
    (τ π : Ω → WithTop ℕ)
    (hτ : IsStoppingTime 𝓖 τ) (hπ : IsStoppingTime 𝓖 π)
    (hle : τ ≤ π) (N : ℕ) (hbdd : ∀ ω, π ω ≤ (N : WithTop ℕ)) :
    (∫ ω, stoppedValue
      (fun (n : ℕ) (w : Ω) =>
        Real.exp (θ * X.X (e n) w -
          (e n : ℝ) * laplaceExponent X.c X.σ X.ν θ)) τ ω ∂P) ≤
    (∫ ω, stoppedValue
      (fun (n : ℕ) (w : Ω) =>
        Real.exp (θ * X.X (e n) w -
          (e n : ℝ) * laplaceExponent X.c X.σ X.ν θ)) π ω ∂P) := by
  subst 𝓖
  exact
    (chat01_levy_exponential_nat_sampled_martingale
      X θ hθ e he).submartingale.expected_stoppedValue_mono
      hτ hπ hle hbdd
