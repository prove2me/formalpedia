-- Prove2me | solution 1 for AvramDividend.Classical.stieltjes_zero_nonpositive_of_zero_atBot_and_origin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:39:22.280457+00:00
-- url     : https://prove2.me/submissions/d1916256-bb15-4347-8576-8c20f3924c19

import Mathlib.MeasureTheory.Measure.Stieltjes

open MeasureTheory Set Filter Topology
open scoped ENNReal
theorem solution
    (f : StieltjesFunction ℝ)
    (hbot : Filter.Tendsto (f : ℝ → ℝ)
      Filter.atBot (nhds (0 : ℝ)))
    (hzero : f 0 = 0) :
    f.measure (Set.Iic (0 : ℝ)) = 0 := by
  rw [f.measure_Iic hbot 0, hzero, sub_zero, ENNReal.ofReal_zero]
