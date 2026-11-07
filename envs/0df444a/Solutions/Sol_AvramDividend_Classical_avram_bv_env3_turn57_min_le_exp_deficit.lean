-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn57_min_le_exp_deficit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:32:03.981196+00:00
-- url     : https://prove2.me/submissions/aaeaea98-1f2f-4f40-8e35-2c42f2cffa34

import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Real

theorem solution (t : ℝ) (ht : 0 ≤ t) :
    min 1 t ≤ 2 * (1 - Real.exp (-t)) := by
  have hexp : 1 + t ≤ Real.exp t := by
    simpa [add_comm] using Real.add_one_le_exp t
  have hepos : 0 < Real.exp (-t) := Real.exp_pos _
  have hmul : (1 + t) * Real.exp (-t) ≤ 1 := by
    calc
      (1 + t) * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right hexp (le_of_lt hepos)
      _ = Real.exp (t + -t) := (Real.exp_add t (-t)).symm
      _ = 1 := by simp
  rcases le_total t 1 with hle | hge
  · rw [min_eq_right hle]
    by_contra hbad
    have hpositive : 0 < t - 2 * (1 - Real.exp (-t)) := by linarith
    have hprod := mul_pos (show 0 < 1 + t by linarith) hpositive
    have hsquare := mul_nonneg ht (sub_nonneg.mpr hle)
    nlinarith
  · rw [min_eq_left hge]
    have hext := mul_nonneg (sub_nonneg.mpr hge) (le_of_lt hepos)
    nlinarith [hmul, hext]
