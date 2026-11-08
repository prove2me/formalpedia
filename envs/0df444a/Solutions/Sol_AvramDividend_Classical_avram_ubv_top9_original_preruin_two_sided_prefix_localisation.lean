-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_preruin_two_sided_prefix_localisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:04:11.122972+00:00
-- url     : https://prove2.me/submissions/d997bde2-bfaa-41fa-abea-b26e091ccadd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_uniform_prefix_upcross_reserve_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_uniform_prefix_preruin_compact_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- True bounded upcross stopping clocks also bound the physical surviving path below. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n) :
    ∃ κ : ℕ → Ω → ℝ≥0,
      (∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (κ j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, κ j ω ≤ ρ ω) ∧
      (∀ j ω (t : ℝ≥0), t ≤ κ j ω →
        X.X t ω ≤ (j : ℝ) + 1 ∧
        ((t : ℝ≥0∞) < ruinTime X x D ω →
          X.X t ω ∈ Icc (-x) ((j : ℝ) + 1) ∧
          riskProcess X x D t ω ∈ Icc 0 (x + ((j : ℝ) + 1)))) ∧
      (∀ ω, ∀ᶠ j : ℕ in atTop, κ j ω = ρ ω) := by
  obtain ⟨κ, hStop, hLe, hFull, hEventually⟩ :=
    avram_ubv_top9_original_uniform_prefix_upcross_reserve_envelope
      X x D hD n ρ hρstop hρle
  refine ⟨κ, hStop, hLe, ?_, hEventually⟩
  intro j ω t ht
  constructor
  · exact (hFull j ω t ht).1
  · intro hPre
    exact avram_ubv_top9_original_uniform_prefix_preruin_compact_band
      X x D hD (κ j) ((j : ℝ) + 1)
      (fun ω' t' ht' => (hFull j ω' t' ht').1)
      ω t ht hPre
