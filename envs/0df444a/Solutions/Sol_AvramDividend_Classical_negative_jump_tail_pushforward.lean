-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_tail_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:23:56.851703+00:00
-- url     : https://prove2.me/submissions/6598b3ac-84e0-4d73-98a8-1427aa69fc68

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

open MeasureTheory Set NNReal ENNReal in
theorem solution (ν : Measure ℝ) (t : ℝ) (ht : 0 < t) :
    (Measure.map (fun y : ℝ => Real.toNNReal (-y)) ν)
      {z : ℝ≥0 | t < (z : ℝ)} = ν (Iio (-t)) := by
  have hf : Measurable (fun y : ℝ => Real.toNNReal (-y)) :=
    measurable_neg.real_toNNReal
  have hs : MeasurableSet {z : ℝ≥0 | t < (z : ℝ)} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [Measure.map_apply hf hs]
  congr 1
  ext y
  simp only [mem_preimage, mem_ofPred_eq, mem_Iio, Real.coe_toNNReal']
  constructor
  · intro h
    rcases le_total (-y) 0 with h0 | h0
    · rw [max_eq_right h0] at h; linarith
    · rw [max_eq_left h0] at h; linarith
  · intro h
    rw [max_eq_left (by linarith)]
    linarith
