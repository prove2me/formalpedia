-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_uniform_discounted_early_ruin_mark_missing_nonlinear_jump_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:11:57.314474+00:00
-- url     : https://prove2.me/submissions/fddea10e-b886-425c-889a-02adaad6cbd0

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_nonlinear_ruin_jump_correction_strictly_positive_against_unitmark
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open AvramDividend.Classical
noncomputable section
theorem solution
    (y σ q : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5)
    (hσ : 0 ≤ σ) (hσearly : σ ≤ 1 / 500)
    (hq : 0 ≤ q) :
    (19 / 25 : ℝ) * Real.exp (-(q / 500)) ≤
      Real.exp (-(q * σ)) *
        ((if y - 2 < 0 then 0 else 1 + (y - 2) + (y - 2) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) -
          (-2 : ℝ)) ∧
    0 < Real.exp (-(q * σ)) *
        ((if y - 2 < 0 then 0 else 1 + (y - 2) + (y - 2) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) -
          (-2 : ℝ)) := by
  have hGap :=
    avram_jump6_A_nonlinear_ruin_jump_correction_strictly_positive_against_unitmark
      y hy hcap
  have hExpPos : 0 < Real.exp (-(q * σ)) := Real.exp_pos _
  have hEarlyExp : Real.exp (-(q / 500)) ≤ Real.exp (-(q * σ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hσearly)]
  have hCompare : (19 / 25 : ℝ) * Real.exp (-(q / 500)) ≤
    (19 / 25 : ℝ) * Real.exp (-(q * σ)) :=
    mul_le_mul_of_nonneg_left hEarlyExp (by norm_num)
  have hEnd := mul_le_mul_of_nonneg_left hGap (le_of_lt hExpPos)
  have hMain : (19 / 25 : ℝ) * Real.exp (-(q / 500)) ≤
      Real.exp (-(q * σ)) *
        ((if y - 2 < 0 then 0 else 1 + (y - 2) + (y - 2) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) - (-2 : ℝ)) := by
    calc
      _ ≤ _ := hCompare
      _ = _ := mul_comm _ _
      _ ≤ _ := hEnd
  constructor
  · exact hMain
  · exact lt_of_lt_of_le
      (mul_pos (by norm_num) (Real.exp_pos _)) hMain
