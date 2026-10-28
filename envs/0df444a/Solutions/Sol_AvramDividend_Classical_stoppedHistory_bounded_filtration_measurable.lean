-- Prove2me | solution 1 for AvramDividend.Classical.stoppedHistory_bounded_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:27:13.87717+00:00
-- url     : https://prove2.me/submissions/bd11f9b1-f1ee-4a30-8918-4ef421540078

import Mathlib.Probability.Process.Stopping

open MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    MeasurableSet[𝓕 T] A := by
  have e : A ∩ {ω : Ω | τ ω ≤ T} = A := Set.inter_eq_left.2 fun ω _ => hbound ω
  rw [← e]
  exact hA T
