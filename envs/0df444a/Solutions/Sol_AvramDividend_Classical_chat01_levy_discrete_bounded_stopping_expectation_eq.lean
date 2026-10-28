-- Prove2me | solution 1 for AvramDividend.Classical.chat01_levy_discrete_bounded_stopping_expectation_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:32:31.522495+00:00
-- url     : https://prove2.me/submissions/d6ff47ed-9a80-49ed-b1da-6ce6cbb507ec

import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq
open AvramDividend.Classical MeasureTheory
open scoped NNReal
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
          (e n : ℝ) * laplaceExponent X.c X.σ X.ν θ)) τ ω ∂P) =
    (∫ ω, stoppedValue
      (fun (n : ℕ) (w : Ω) =>
        Real.exp (θ * X.X (e n) w -
          (e n : ℝ) * laplaceExponent X.c X.σ X.ν θ)) π ω ∂P) :=
  AvramDividend.Classical.chat01_monotone_sampling_bounded_optional_stopping_eq
    (f := fun t ω => Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) e he
    (AvramDividend.Classical.levy_compensated_exponential_martingale X θ hθ)
    𝓖 h𝓖 τ π hτ hπ hle N hbdd
