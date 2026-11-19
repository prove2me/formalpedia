-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_positive_event_budget_to_centred_masked_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:53:30.010209+00:00
-- url     : https://prove2.me/submissions/4df0dffa-7f78-4798-99f3-b01adc2a3c8f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian11_conditional_budget_zero_clock_centering
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (hPos : 0 < (P A).toReal)
    (f : Ω → ℝ) (hf : Integrable f P) (b : ℝ)
    (hBudget : (∫ ω in A, f ω ∂P) ≤ b * (P A).toReal) :
    ∃ M G : Ω → ℝ,
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      (∀ ω, ω ∉ A → M ω = 0) ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, ω ∈ A → f ω ≤ b + M ω + G ω) := by
  classical
  obtain ⟨M, hMI, hM0, hOutside, hInside⟩ :=
    AvramDividend.Classical.avram_ubv_gaussian11_conditional_budget_zero_clock_centering
      A hA hPos f hf b hBudget
  refine ⟨M, (fun _ => (0 : ℝ)), hMI, hM0, hOutside, ?_, ?_⟩
  · exact Filter.Eventually.of_forall (fun ω => le_refl (0 : ℝ))
  · exact Filter.Eventually.of_forall (fun ω hw => by
      have hBound := hInside ω hw
      simpa only [add_zero] using hBound)
