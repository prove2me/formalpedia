-- Prove2me | solution 1 for AvramDividend.Classical.measurableSet_countable_schedule_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:27:39.939773+00:00
-- url     : https://prove2.me/submissions/3332d6bb-a8ec-4250-901a-a5fc79430bf4

import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Order.OrderClosed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal

theorem solution
    (times horizons : ℕ → ℝ≥0) :
    MeasurableSet
      {f : ℝ≥0 → ℝ | ∀ n : ℕ, ∃ m : ℕ,
        times m < horizons n ∧ f (times m) < 0} := by
  have hset :
      {f : ℝ≥0 → ℝ | ∀ n : ℕ, ∃ m : ℕ,
        times m < horizons n ∧ f (times m) < 0} =
      (⋂ n : ℕ, ⋃ m : ℕ,
        {f : ℝ≥0 → ℝ | times m < horizons n ∧ f (times m) < 0}) := by
    ext f
    simp
  rw [hset]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m => ?_
  by_cases hmn : times m < horizons n
  · have hm : MeasurableSet
        {f : ℝ≥0 → ℝ | f (times m) < (0 : ℝ)} :=
      isOpen_Iio.measurableSet.preimage (measurable_pi_apply (times m))
    simpa only [hmn, true_and] using hm
  · simp [hmn]
