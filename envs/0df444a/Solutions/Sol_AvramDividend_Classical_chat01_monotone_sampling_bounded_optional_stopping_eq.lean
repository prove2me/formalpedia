-- Prove2me | solution 1 for AvramDividend.Classical.chat01_monotone_sampling_bounded_optional_stopping_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:40:58.094607+00:00
-- url     : https://prove2.me/submissions/53ff70bb-c210-48a3-a9a3-72b5f268eba9

import Mathlib.Probability.Martingale.OptionalStopping
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal

/-- Bounded optional stopping preserves the expectation of a martingale
    sampled at any increasing sequence of times. -/
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
    (∫ ω, stoppedValue (fun (n : ℕ) => f (e n)) τ ω ∂μ) =
      (∫ ω, stoppedValue (fun (n : ℕ) => f (e n)) π ω ∂μ) := by
  have hforward :=
    chat01_monotone_sampling_bounded_optional_stopping
      e he hf 𝓖 h𝓖 τ π hτ hπ hle N hbdd
  have hneg :=
    chat01_monotone_sampling_bounded_optional_stopping
      e he hf.neg 𝓖 h𝓖 τ π hτ hπ hle N hbdd
  have hback :
      (∫ ω, stoppedValue (fun (n : ℕ) => f (e n)) π ω ∂μ) ≤
      (∫ ω, stoppedValue (fun (n : ℕ) => f (e n)) τ ω ∂μ) := by
    change
      (∫ ω, stoppedValue (-(fun (n : ℕ) => f (e n))) τ ω ∂μ) ≤
      (∫ ω, stoppedValue (-(fun (n : ℕ) => f (e n))) π ω ∂μ) at hneg
    have hneg' := neg_le_neg hneg
    simpa only [stoppedValue_neg, Pi.neg_apply, integral_neg, neg_neg] using hneg'
  exact le_antisymm hforward hback
