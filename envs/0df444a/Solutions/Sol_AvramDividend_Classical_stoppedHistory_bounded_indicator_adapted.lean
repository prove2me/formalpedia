-- Prove2me | solution 1 for AvramDividend.Classical.stoppedHistory_bounded_indicator_adapted
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:45:30.509022+00:00
-- url     : https://prove2.me/submissions/d04621cf-e38b-44c9-95f6-126e21a265cb

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_bounded_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    Measurable[𝓕 T]
      (Set.indicator A (fun _ : Ω => (1 : ℝ))) :=
  measurable_const.indicator
    (AvramDividend.Classical.stoppedHistory_bounded_filtration_measurable τ A hA T hbound)
