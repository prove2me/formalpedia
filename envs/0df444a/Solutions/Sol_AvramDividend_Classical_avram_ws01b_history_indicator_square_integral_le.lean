-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_history_indicator_square_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:45:44.378884+00:00
-- url     : https://prove2.me/submissions/8efd9805-3873-400f-811d-6a84ba1e0fc5

import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- An actual killed-history indicator cannot increase a nonnegative second moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (s : Set Ω) (hs : MeasurableSet s)
    (hfi : Integrable (fun ω => (f ω)^2) P) :
    Integrable (fun ω => (s.indicator f ω)^2) P ∧
      (∫ ω, (s.indicator f ω)^2 ∂P) ≤ ∫ ω, (f ω)^2 ∂P := by
  have hsq : (fun ω => (s.indicator f ω)^2) =
      s.indicator (fun ω => (f ω)^2) := by
    funext ω
    by_cases h : ω ∈ s
    · simp only [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  constructor
  · rw [hsq]
    exact hfi.indicator hs
  · rw [hsq]
    apply integral_mono (hfi.indicator hs) hfi
    intro ω
    by_cases h : ω ∈ s
    · simp only [Set.indicator_of_mem h, le_refl]
    · simpa only [Set.indicator_of_notMem h] using sq_nonneg (f ω)
