-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_above_positive_time_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:23:18.499534+00:00
-- url     : https://prove2.me/submissions/40dc9182-a239-47d6-bac3-16e8eecb5ebd

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Above the barrier, the initial dividend excess is paid for every positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (hax : a < x) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    barrierStrategy X x a t ω =
      (x - a) + barrierStrategy X a a t ω := by
  rw [barrierStrategy_eq_add_initial_excess_above_barrier X x a ha hax]
  simp [ne_of_gt ht]
