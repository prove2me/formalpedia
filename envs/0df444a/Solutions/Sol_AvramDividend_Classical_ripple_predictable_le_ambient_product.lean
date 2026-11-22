-- Prove2me | solution 1 for AvramDividend.Classical.ripple_predictable_le_ambient_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:12:19.426864+00:00
-- url     : https://prove2.me/submissions/9b4b8c87-84e3-41bc-a992-3ed60ba6c2b5

import Mathlib

open MeasureTheory Set
open scoped NNReal

/-- Each predictable generating rectangle is product measurable.
Bridge for Ripple's stopped L² machinery (Apache-2.0, Ripple commit
e216e28ce3ffb43877e11f71be260e40a37a35df). -/
theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 mΩ) :
    F.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
  unfold Filtration.predictable
  apply MeasurableSpace.generateFrom_le
  intro s hs
  rcases hs with ⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩
  · exact (measurableSet_singleton (0 : ℝ≥0)).prod ((F.le 0) _ hA)
  · exact measurableSet_Ioi.prod ((F.le i) _ hA)

