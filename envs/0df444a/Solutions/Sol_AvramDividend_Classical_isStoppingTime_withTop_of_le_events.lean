-- Prove2me | solution 1 for AvramDividend.Classical.isStoppingTime_withTop_of_le_events
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:50:26.36802+00:00
-- url     : https://prove2.me/submissions/e7e8c1e1-744b-48ca-9aba-3ea874e81396

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- Stopping-time measurability with finite-valued nonnegative times coerced to WithTop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s}) :
    IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) := by
  intro s
  simpa only [WithTop.coe_le_coe] using hτ s

