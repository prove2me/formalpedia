-- Prove2me | solution 1 for AvramDividend.Classical.stoppedHistory_measurable_of_equal_finite_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:51:50.503437+00:00
-- url     : https://prove2.me/submissions/269c39cc-f8d2-49e0-91f7-989b8a6b9f56

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Equal extended clocks define the same stopped-history sigma algebra. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (T : Ω → ℝ≥0∞) (hT : IsStoppingTime 𝓕 T)
    (hEq : ∀ ω : Ω, (τ ω : ℝ≥0∞) = T ω)
    (A : Set Ω) (hA : MeasurableSet[hT.measurableSpace] A) :
    MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A := by
  have hClock : (fun ω : Ω => (τ ω : ℝ≥0∞)) = T := funext hEq
  cases hClock
  exact hA