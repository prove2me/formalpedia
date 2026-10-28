-- Prove2me | solution 2 for AvramDividend.Classical.stoppedHistory_measurable_of_equal_finite_clocks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:52:03.294109+00:00
-- url     : https://prove2.me/submissions/58f51d84-fcc8-48f1-9a31-4f7b56429290

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (T : Ω → ℝ≥0∞) (hT : IsStoppingTime 𝓕 T)
    (hEq : ∀ ω : Ω, (τ ω : ℝ≥0∞) = T ω)
    (A : Set Ω) (hA : MeasurableSet[hT.measurableSpace] A) :
    MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A := by 
  obtain rfl : T = fun ω => (τ ω : ℝ≥0∞) := (funext hEq).symm
  exact hA
