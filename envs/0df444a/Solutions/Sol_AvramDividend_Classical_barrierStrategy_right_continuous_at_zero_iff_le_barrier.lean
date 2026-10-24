-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_right_continuous_at_zero_iff_le_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:41:23.671848+00:00
-- url     : https://prove2.me/submissions/0de16a4e-86d1-4709-9103-6ccb6f6b7d9c

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_not_right_continuous_at_zero_above_barrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The positive initial lump sum is exactly the obstruction to right continuity at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (ω : Ω) :
    ContinuousWithinAt
      (fun s => barrierStrategy X x a s ω) (Ici (0 : ℝ≥0)) 0 ↔
      x ≤ a := by
  constructor
  · intro hc
    by_contra hxa
    exact (barrierStrategy_not_right_continuous_at_zero_above_barrier
      X x a ha (lt_of_not_ge hxa) ω) hc
  · intro hxa
    exact barrierStrategy_right_continuous_of_le X x a hxa ω 0
