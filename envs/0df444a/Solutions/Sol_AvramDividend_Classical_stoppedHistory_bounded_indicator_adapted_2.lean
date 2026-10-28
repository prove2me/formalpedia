-- Prove2me | solution 2 for AvramDividend.Classical.stoppedHistory_bounded_indicator_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:46:03.408406+00:00
-- url     : https://prove2.me/submissions/196aaa81-6d0d-4e49-ad5e-b545ad0ef117

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_bounded_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The indicator of a bounded stopped-history event is observable at the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    Measurable[𝓕 T]
      (Set.indicator A (fun _ : Ω => (1 : ℝ))) := by
  exact measurable_const.indicator
    (stoppedHistory_bounded_filtration_measurable τ A hA T hbound)
