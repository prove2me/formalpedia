-- Prove2me | solution 1 for AvramDividend.Classical.barrierSuccessfulClockCutoff_stoppedHistory
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:17:13.220534+00:00
-- url     : https://prove2.me/submissions/465b1aae-8232-4d85-874a-dcb5b1abb3d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ σ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hσ : IsStoppingTime 𝓕.rightCont σ)
    (N s : ℝ≥0) :
    MeasurableSet[𝓕.rightCont s]
      (({ω | τ ω < σ ω} ∩ {ω | τ ω ≤ (N : ℝ≥0∞)}) ∩
        {ω | min (τ ω) (N : ℝ≥0∞) ≤ (s : ℝ≥0∞)}) := by
  have hset : {ω | τ ω < σ ω} = {ω | σ ω ≤ τ ω}ᶜ := by
    ext ω
    show τ ω < σ ω ↔ ¬ σ ω ≤ τ ω
    exact lt_iff_not_ge
  have hA : MeasurableSet[hτ.measurableSpace] {ω | τ ω < σ ω} := by
    rw [hset]
    exact (IsStoppingTime.measurableSet_stopping_time_le hσ hτ).compl
  rw [hτ.measurableSet] at hA
  rcases le_or_gt N s with hNs | hsN
  · have : ({ω | τ ω < σ ω} ∩ {ω | τ ω ≤ (N : ℝ≥0∞)}) ∩
        {ω | min (τ ω) (N : ℝ≥0∞) ≤ (s : ℝ≥0∞)} = {ω | τ ω < σ ω} ∩ {ω | τ ω ≤ (N : ℝ≥0∞)} := by
      ext ω
      simp only [mem_inter_iff, mem_setOf_eq, and_iff_left_iff_imp]
      intro _
      exact (min_le_right _ _).trans (by exact_mod_cast hNs)
    rw [this]
    exact (𝓕.rightCont.mono hNs) _ (hA.2 N)
  · have : ({ω | τ ω < σ ω} ∩ {ω | τ ω ≤ (N : ℝ≥0∞)}) ∩
        {ω | min (τ ω) (N : ℝ≥0∞) ≤ (s : ℝ≥0∞)} = {ω | τ ω < σ ω} ∩ {ω | τ ω ≤ (s : ℝ≥0∞)} := by
      ext ω
      have hsN' : (s : ℝ≥0∞) < N := by exact_mod_cast hsN
      simp only [mem_inter_iff, mem_setOf_eq, min_le_iff]
      constructor
      · rintro ⟨⟨h1, _⟩, h3 | h3⟩
        · exact ⟨h1, h3⟩
        · exact absurd h3 (not_le.mpr hsN')
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans hsN'.le⟩, Or.inl h2⟩
    rw [this]
    exact hA.2 s
