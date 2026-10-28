-- Prove2me | solution 1 for AvramDividend.Classical.strict_stopping_order_event_stoppedHistory
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:16:34.941534+00:00
-- url     : https://prove2.me/submissions/ed017c17-d222-4135-9b5b-7fa3bb7a2846

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ σ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕 τ)
    (hσ : IsStoppingTime 𝓕 σ)
    (s : ℝ≥0) :
    MeasurableSet[𝓕 s]
      ({ω : Ω | τ ω < σ ω} ∩
        {ω : Ω | τ ω ≤ (s : ℝ≥0∞)}) := by
  have h := (IsStoppingTime.measurableSet_stopping_time_le hσ hτ).compl
  have h2 := h.2 s
  convert h2 using 2
  · ext ω
    exact (not_le (a := σ ω) (b := τ ω)).symm
  · rfl
