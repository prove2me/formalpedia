-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_right_continuous_all_times_iff_le_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:46:54.801362+00:00
-- url     : https://prove2.me/submissions/1b714f28-1947-4f55-97b0-057b33cb9d5e

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_not_right_continuous_at_zero_above_barrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- All-time right continuity is equivalent to having no initial excess dividend. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (ω : Ω) :
    (∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t) ↔
      x ≤ a := by
  constructor
  · intro hcont
    by_contra hxa
    exact (barrierStrategy_not_right_continuous_at_zero_above_barrier
      X x a ha (lt_of_not_ge hxa) ω) (hcont 0)
  · intro hxa t
    exact barrierStrategy_right_continuous_of_le X x a hxa ω t
