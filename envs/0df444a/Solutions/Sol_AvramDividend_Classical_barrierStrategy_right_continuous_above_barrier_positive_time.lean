-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_right_continuous_above_barrier_positive_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:23:28.463279+00:00
-- url     : https://prove2.me/submissions/939c70c2-9ba1-41df-8285-ac4eaf96bfe3

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Dividend right-continuity holds away from the initial lump-sum jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (hax : a < x) (ω : Ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t := by
  have hf (s : ℝ≥0) (hs : 0 < s) :
      barrierStrategy X x a s ω =
        (x - a) + barrierStrategy X a a s ω := by
    rw [barrierStrategy_eq_add_initial_excess_above_barrier X x a ha hax]
    simp [ne_of_gt hs]
  have hevent :
      (fun s : ℝ≥0 => barrierStrategy X x a s ω) =ᶠ[𝓝[Ici t] t]
        (fun s : ℝ≥0 => (x - a) + barrierStrategy X a a s ω) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hf s (lt_of_lt_of_le ht hs)
  have hcontinuous :
      ContinuousWithinAt
        (fun s : ℝ≥0 => (x - a) + barrierStrategy X a a s ω)
        (Ici t) t :=
    continuousWithinAt_const.add (barrierStrategy_right_continuous X a ω t)
  change Tendsto (fun s : ℝ≥0 => barrierStrategy X x a s ω)
      (𝓝[Ici t] t) (𝓝 (barrierStrategy X x a t ω))
  rw [hf t ht]
  exact hcontinuous.congr' hevent.symm
