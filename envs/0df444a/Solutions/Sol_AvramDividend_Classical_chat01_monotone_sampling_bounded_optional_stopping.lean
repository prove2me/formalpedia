-- Prove2me | solution 1 for AvramDividend.Classical.chat01_monotone_sampling_bounded_optional_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:17:47.852812+00:00
-- url     : https://prove2.me/submissions/fe4806d1-deac-4bf0-948d-3f03b5193077

import Mathlib.Probability.Martingale.OptionalStopping
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_nat_sampling_martingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal

/-- Bounded discrete optional stopping for a real-time martingale sampled
    along an increasing sequence of times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {f : ℝ≥0 → Ω → ℝ}
    (e : ℕ → ℝ≥0) (he : Monotone e) (hf : Martingale f 𝓕 μ)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration μ 𝓖]
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
    (∫ ω, stoppedValue (fun (n : ℕ) => f (e n)) τ ω ∂μ) ≤
      (∫ ω, stoppedValue (fun (n : ℕ) => f (e n)) π ω ∂μ) := by
  subst 𝓖
  exact ((chat01_monotone_nat_sampling_martingale e he hf).submartingale).expected_stoppedValue_mono
    hτ hπ hle hbdd
