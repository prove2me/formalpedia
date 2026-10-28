-- Prove2me | solution 1 for AvramDividend.Classical.downward_grid_limsup_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:03:15.678403+00:00
-- url     : https://prove2.me/submissions/1d5a66c8-c3f4-42f5-add7-92bc009b31d2

import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal

/--
For any sequence of finite observation grids, the paths showing downward
increments beyond a threshold on infinitely many grids form a measurable set.
-/
theorem solution
    (grid : ℕ → Finset (ℝ≥0 × ℝ≥0)) (a : ℝ) :
    MeasurableSet
      (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n},
        ⋃ ij ∈ grid n.1,
          {f : ℝ≥0 → ℝ | f ij.2 - f ij.1 < -a}) := by
  apply MeasurableSet.iInter
  intro N
  apply MeasurableSet.iUnion
  intro n
  refine Finset.measurableSet_biUnion (grid n.1) ?_
  intro ij hij
  have hm1 : Measurable (fun f : ℝ≥0 → ℝ => f ij.1) :=
    measurable_pi_apply _
  have hm2 : Measurable (fun f : ℝ≥0 → ℝ => f ij.2) :=
    measurable_pi_apply _
  change MeasurableSet ((fun f : ℝ≥0 → ℝ => f ij.2 - f ij.1) ⁻¹' Iio (-a))
  exact (isOpen_Iio.measurableSet).preimage (hm2.sub hm1)
