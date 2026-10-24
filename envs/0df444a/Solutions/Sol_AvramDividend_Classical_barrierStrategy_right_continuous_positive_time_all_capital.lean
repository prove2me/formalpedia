-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_right_continuous_positive_time_all_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:29:36.679321+00:00
-- url     : https://prove2.me/submissions/1cc00e97-4999-4fe1-9b70-9921798113c7

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_above_barrier_positive_time
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Right continuity at positive times for all starting capital, with an initial jump allowed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t := by
  by_cases hxa : x ≤ a
  · exact barrierStrategy_right_continuous_of_le X x a hxa ω t
  · exact barrierStrategy_right_continuous_above_barrier_positive_time
      X x a ha (lt_of_not_ge hxa) ω t ht
