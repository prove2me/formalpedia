-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_discounted_original_first_negative_size2_mark_nonlinear_compensation_positive_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:07:26.127192+00:00
-- url     : https://prove2.me/submissions/233de5a1-e39a-4048-8dec-d1b722d994b9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_nonlinear_ruin_jump_correction_strictly_positive_against_unitmark
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open AvramDividend.Classical
noncomputable section
theorem solution
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5)
    (τ q : ℝ) :
    (19 / 25 : ℝ) * Real.exp (-(q * τ)) ≤
      Real.exp (-(q * τ)) *
        ((if y - 2 < 0 then 0
          else 1 + (y - 2) + (y - 2) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) -
           (-2 : ℝ)) ∧
    0 < Real.exp (-(q * τ)) *
        ((if y - 2 < 0 then 0
          else 1 + (y - 2) + (y - 2) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) -
           (-2 : ℝ)) := by
  have hGap :=
    avram_jump6_A_nonlinear_ruin_jump_correction_strictly_positive_against_unitmark
      y hy hcap
  have hExp : 0 < Real.exp (-(q * τ)) := Real.exp_pos _
  have hLower :
      (19 / 25 : ℝ) * Real.exp (-(q * τ)) ≤
        ((if y - 2 < 0 then 0
          else 1 + (y - 2) + (y - 2) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) -
           (-2 : ℝ)) * Real.exp (-(q * τ)) :=
    mul_le_mul_of_nonneg_right hGap (le_of_lt hExp)
  have hPos : 0 < (19 / 25 : ℝ) * Real.exp (-(q * τ)) :=
    mul_pos (by norm_num) hExp
  constructor
  · calc
      _ ≤ _ := hLower
      _ = _ := mul_comm _ _
  · calc
      0 < _ := lt_of_lt_of_le hPos hLower
      _ = _ := mul_comm _ _
