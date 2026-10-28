-- Prove2me | solution 1 for AvramDividend.Classical.stoppedHistory_indicator_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:05:05.889786+00:00
-- url     : https://prove2.me/submissions/2e9b1da1-c0d2-4bce-bdd6-0c78590d42a9

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Indicators of finite stopped-history events are globally measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    Measurable (Set.indicator A (fun _ : Ω => (1 : ℝ))) := by
  exact measurable_const.indicator
    (stoppedHistory_event_measurable τ A hA)
