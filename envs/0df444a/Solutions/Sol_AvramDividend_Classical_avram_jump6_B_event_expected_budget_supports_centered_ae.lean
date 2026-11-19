-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_event_expected_budget_supports_centered_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:50:57.07221+00:00
-- url     : https://prove2.me/submissions/76873756-0df1-4597-85ca-3795a26be4b8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_positive_clock_supported_centered_of_expected
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (F : Ω → ℝ) (hFI : Integrable F P)
    (b : ℝ)
    (hBudget : (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal) :
    ∃ M : Ω → ℝ,
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, ω ∉ A → M ω = 0) ∧
      (∀ᵐ ω ∂P, ω ∈ A → F ω ≤ b + M ω) := by
  classical
  by_cases hp : 0 < (P A).toReal
  · obtain ⟨M, hMI, hMean, hOff, hUpper⟩ :=
      avram_mix_inf20_positive_clock_supported_centered_of_expected
        A hA F hFI b hp hBudget
    refine ⟨M, hMI, hMean, ?_, ?_⟩
    · exact Filter.Eventually.of_forall (fun ω hω => hOff ω hω)
    · exact Filter.Eventually.of_forall (fun ω hω => hUpper ω hω)
  · have hpzero : (P A).toReal = 0 := by
      exact le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
    have hpfinite : P A < ⊤ := by
      exact lt_of_le_of_lt (measure_mono (subset_univ A)) (by simp)
    have hPA : P A = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (P A)).mp hpzero with h | h
      · exact h
      · exact False.elim ((ne_of_lt hpfinite) h)
    have hNotA : ∀ᵐ ω ∂P, ω ∉ A := by
      have h := (ae_iff).mpr (show P (Aᶜ)ᶜ = 0 by simpa using hPA)
      simpa only [compl_compl, mem_compl_iff] using h
    refine ⟨(fun _ : Ω => 0), by simp, by simp, ?_, ?_⟩
    · exact Filter.Eventually.of_forall (fun _ _ => rfl)
    · filter_upwards [hNotA] with ω hω
      intro hmem
      exact False.elim (hω hmem)
