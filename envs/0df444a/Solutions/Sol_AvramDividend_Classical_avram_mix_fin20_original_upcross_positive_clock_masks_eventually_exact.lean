-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin20_original_upcross_positive_clock_masks_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:32:52.539205+00:00
-- url     : https://prove2.me/submissions/d2e6c3f3-e5b3-473f-ab64-d88af7a96442

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_upcross_localisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℝ≥0)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n) :
    ∃ κ : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (κ k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, κ k ω ≤ ρ ω) ∧
      (∀ k ω, X.X (κ k ω) ω ≤ (k : ℝ) + 1) ∧
      (∀ ω, ∀ᶠ k : ℕ in atTop,
        κ k ω = ρ ω ∧
          (κ k ω ≠ 0 ↔ ρ ω ≠ 0)) := by
  classical
  obtain ⟨κ, hStop, hLe, hBound, hEventually⟩ :=
    avram_ubv_top9_original_any_clock_upcross_localisation
      X n ρ hρstop hρle
  refine ⟨κ, hStop, hLe, hBound, ?_⟩
  intro ω
  filter_upwards [hEventually ω] with k hk
  exact ⟨hk, by rw [hk]⟩
