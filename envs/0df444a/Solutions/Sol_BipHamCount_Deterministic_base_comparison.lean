-- Prove2me | solution 1 for BipHamCount.Deterministic.base_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:05:21.034577+00:00
-- url     : https://prove2.me/submissions/e750ecb5-b5eb-4cbe-9892-d8d1dc079231

import Definitions.Def_BipHamCount_Deterministic_Core

open BipHamCount.Deterministic

set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

private theorem log_left : Real.log (100000 / 60909 : ℝ) ≤ (49579 / 100000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (39091 / 160909 : ℝ)) (by norm_num) (by norm_num) 11
  rw [show (1 + (39091 / 160909 : ℝ)) / (1 - (39091 / 160909 : ℝ)) = (100000 / 60909 : ℝ) by norm_num] at h
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

private theorem log_right : Real.log (100000 / 39091 : ℝ) ≤ (939279 / 1000000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (60909 / 139091 : ℝ)) (by norm_num) (by norm_num) 11
  rw [show (1 + (60909 / 139091 : ℝ)) / (1 - (60909 / 139091 : ℝ)) = (100000 / 39091 : ℝ) by norm_num] at h
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

private theorem log_three : Real.log (3 : ℝ) ≤ (549307 / 500000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 11
  rw [show (1 + (1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) = (3 : ℝ) by norm_num] at h
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

private theorem log_base : (669161 / 1000000 : ℝ) ≤ Real.log (9763 / 5000 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (4763 / 14763 : ℝ)) (by norm_num) (by norm_num) 11
  rw [show (1 + (4763 / 14763 : ℝ)) / (1 - (4763 / 14763 : ℝ)) = (9763 / 5000 : ℝ) by norm_num] at h
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem solution :
    Real.exp (Real.binEntropy alpha) < (19526/10000 : ℝ) ∧
    Real.exp (Real.binEntropy alpha / 2) * (3 : ℝ) ^ (alpha / 2) <
      (19526/10000 : ℝ) := by
  have he : Real.binEntropy alpha ≤ (669155 : ℝ) / 1000000 := by
    rw [Real.binEntropy, alpha]
    rw [show ((60909 / 100000 : ℝ))⁻¹ = 100000 / 60909 by norm_num,
        show (1 - (60909 / 100000 : ℝ))⁻¹ = 100000 / 39091 by norm_num]
    linarith only [log_left, log_right]
  have hb := log_base
  rw [← show (19526/10000 : ℝ) = 9763/5000 by norm_num] at hb
  constructor
  · apply (Real.log_lt_log_iff (Real.exp_pos _) (by norm_num)).mp
    rw [Real.log_exp]
    linarith only [he, hb]
  · apply (Real.log_lt_log_iff (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num)).mp
    rw [Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) _).ne',
      Real.log_exp, Real.log_rpow (by norm_num : (0:ℝ) < 3), alpha]
    unfold alpha at he
    linarith only [he, log_three, hb]
