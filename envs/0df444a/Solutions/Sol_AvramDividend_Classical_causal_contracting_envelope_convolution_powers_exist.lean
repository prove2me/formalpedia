-- Prove2me | solution 1 for AvramDividend.Classical.causal_contracting_envelope_convolution_powers_exist
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:40:45.279873+00:00
-- url     : https://prove2.me/submissions/74a47947-8c62-4fc5-b710-8ad56b9165a6

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_exists_contracting_weighted_envelope
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_sequence_exists

open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A contracting causal envelope has integrable convolution powers. -/
theorem solution
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ (w : ℝ) (κ : ℝ → ℝ),
      0 < w ∧
      κ = (fun t : ℝ => a⁻¹ * Real.exp (-w * t) * (|β| + K t)) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) < 1 ∧
      ∃ F : ℕ → ℝ → ℝ,
        F 0 = κ ∧
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
            κ s * F n (x - s) ∂volume) ∧
        (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
        (∀ n : ℕ,
          (∫ x in Ioi (0 : ℝ), F (n + 1) x ∂volume) =
          (∫ x in Ioi (0 : ℝ), κ x ∂volume) *
            (∫ x in Ioi (0 : ℝ), F n x ∂volume)) := by
  obtain ⟨w, hw, hI, hmass⟩ :=
    causal_l1_exists_contracting_weighted_envelope K a β ha hK
  let κ : ℝ → ℝ :=
    fun t => a⁻¹ * Real.exp (-w * t) * (|β| + K t)
  obtain ⟨F, hzero, hstep, hIF, hrec⟩ :=
    causal_l1_convolution_power_sequence_exists κ hI
  exact ⟨w, κ, hw, rfl, hI, hmass,
    F, hzero, hstep, hIF, hrec⟩
