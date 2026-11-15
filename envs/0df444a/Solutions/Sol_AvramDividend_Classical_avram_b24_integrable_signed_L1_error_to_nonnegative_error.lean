-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_integrable_signed_L1_error_to_nonnegative_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:46:06.628971+00:00
-- url     : https://prove2.me/submissions/17b64d93-9c4f-4dcb-bf01-10acd0121ba5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_signed_ito_ledger_error_controls_positive_cash_gap_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (E : ℕ → Ω → ℝ)
    (hEI : ∀ k, Integrable (E k) P)
    (hEC : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        (∫ ω, ‖E m ω‖ ∂P) ≤ ε) :
    ∃ Epos : ℕ → Ω → ℝ,
      (∀ k, Integrable (Epos k) P) ∧
      (∀ k ω, 0 ≤ Epos k ω ∧ E k ω ≤ Epos k ω) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
          (∫ ω, ‖Epos m ω‖ ∂P) ≤ ε) := by
  let Ep : ℕ → Ω → ℝ := fun k ω => max 0 (E k ω)
  have hTransfer (k : ℕ) :
      Integrable (Ep k) P ∧
      (∫ ω, ‖Ep k ω‖ ∂P) ≤ (∫ ω, ‖E k ω‖ ∂P) := by
    have hLed : ∀ᵐ ω ∂P, E k ω ≤
        (0 : ℝ) + (0 : ℝ) + (0 : ℝ) + E k ω :=
      Filter.Eventually.of_forall (fun ω => by simp)
    have h :=
      avram_b24_signed_ito_ledger_error_controls_positive_cash_gap_L1
        (E k) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (E k)
        0 (hEI k) (integrable_zero Ω ℝ P)
        (integrable_zero Ω ℝ P) (hEI k) hLed
    simpa only [Ep, sub_zero] using h
  refine ⟨Ep, (fun k => (hTransfer k).1), ?_, ?_⟩
  · intro k ω
    exact ⟨le_max_left _ _, le_max_right _ _⟩
  · intro ε hε
    obtain ⟨N, hN⟩ := hEC ε hε
    refine ⟨N, ?_⟩
    intro m hm
    exact (hTransfer m).2.trans (hN m hm)
