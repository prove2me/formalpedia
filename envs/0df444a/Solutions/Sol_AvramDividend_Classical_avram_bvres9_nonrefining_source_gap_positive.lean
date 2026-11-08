-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvres9_nonrefining_source_gap_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:59:48.659388+00:00
-- url     : https://prove2.me/submissions/88a9885c-ec37-4ab9-8ee2-6080509ad597

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical
noncomputable section

/-- The persistent grid cell alone forces a positive expected gap. -/
theorem solution :
    (2 : ℝ) < (15 / 4 : ℝ) * Real.exp (-(3 / 100 : ℝ)) *
      Real.exp (-(1 / 2 : ℝ)) := by
  have hbase : (147 / 200 : ℝ) ≤ Real.exp (-(53 / 200 : ℝ)) := by
    nlinarith [Real.add_one_le_exp (-(53 / 200 : ℝ))]
  have hsq : (147 / 200 : ℝ) ^ 2 ≤
      (Real.exp (-(53 / 200 : ℝ))) ^ 2 := by
    have hpos : 0 ≤ Real.exp (-(53 / 200 : ℝ)) + (147 / 200 : ℝ) := by
      positivity
    have hm := mul_nonneg (sub_nonneg.mpr hbase) hpos
    nlinarith
  have hexp : (Real.exp (-(53 / 200 : ℝ))) ^ 2 =
      Real.exp (-(3 / 100 : ℝ)) * Real.exp (-(1 / 2 : ℝ)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    (2 : ℝ) < (15 / 4 : ℝ) * (147 / 200 : ℝ) ^ 2 := by norm_num
    _ ≤ (15 / 4 : ℝ) * (Real.exp (-(53 / 200 : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = (15 / 4 : ℝ) * Real.exp (-(3 / 100 : ℝ)) *
        Real.exp (-(1 / 2 : ℝ)) := by rw [hexp]; ring
