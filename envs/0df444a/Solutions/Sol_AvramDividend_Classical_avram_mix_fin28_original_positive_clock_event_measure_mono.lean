-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin28_original_positive_clock_event_measure_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:06:30.466235+00:00
-- url     : https://prove2.me/submissions/eb719c7f-b0c9-438a-829b-00a583a0f75e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (σ ρ : Ω → ℝ≥0) (hρle : ∀ ω, ρ ω ≤ σ ω)
    (A : Set Ω) :
    P (A ∩ {ω : Ω | ρ ω ≠ 0}) ≤
      P (A ∩ {ω : Ω | σ ω ≠ 0}) := by
  apply measure_mono
  intro ω hω
  refine ⟨hω.1, ?_⟩
  intro hσzero
  have hρzero : ρ ω = 0 := by
    apply le_antisymm
    · simpa [hσzero] using hρle ω
    · exact zero_le
  exact hω.2 hρzero
