-- Prove2me | solution 1 for AvramDividend.Classical.supermartingale_expected_stoppedValue_antitone_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:01:53.193104+00:00
-- url     : https://prove2.me/submissions/9a6df37c-e7ef-412b-8a3c-4ef5a192d0da

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓖 : Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓖]
    {f : ℕ → Ω → ℝ} (hf : Supermartingale f 𝓖 μ)
    {τ π : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝓖 τ) (hπ : IsStoppingTime 𝓖 π)
    (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ (N : WithTop ℕ)) :
    (∫ ω, stoppedValue f π ω ∂μ) ≤
      ∫ ω, stoppedValue f τ ω ∂μ := by
  have h :=
    hf.neg.expected_stoppedValue_mono hτ hπ hle hbdd
  have hneg :
      -(∫ ω, stoppedValue f τ ω ∂μ) ≤
        -(∫ ω, stoppedValue f π ω ∂μ) := by
    simpa only [stoppedValue_neg, Pi.neg_apply, integral_neg] using h
  exact neg_le_neg_iff.mp hneg
