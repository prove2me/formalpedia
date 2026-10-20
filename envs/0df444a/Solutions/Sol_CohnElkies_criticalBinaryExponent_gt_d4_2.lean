-- Prove2me | solution 2 for CohnElkies.criticalBinaryExponent_gt_d4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:26:50.411766+00:00
-- url     : https://prove2.me/submissions/8cada8bb-d2f2-4d40-a08e-9324420e69d0

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open Finset
open CohnElkies


theorem solution :
    (0.6044 : ℝ) < criticalBinaryExponent := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hp := Real.pi_pos
  have hb := Real.exp_bound (x := (0.1447292 : ℝ)) (by rw [abs_of_pos (by norm_num)]; norm_num) (n := 6) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 6, (0.1447292 : ℝ) ^ m / (m.factorial : ℝ)) =
      1 + 0.1447292 + 0.1447292 ^ 2 / 2 + 0.1447292 ^ 3 / 6 + 0.1447292 ^ 4 / 24 + 0.1447292 ^ 5 / 120 := by
    simp [Finset.sum_range_succ, Nat.factorial] <;> norm_num
  rw [hsum, abs_of_pos (by norm_num : (0:ℝ) < 0.1447292)] at hb
  have he1 := Real.exp_one_lt_d9
  have hE : Real.exp 0.1447292 ≤ 1.15572656 := by
    have := (abs_le.1 hb).2
    norm_num [Nat.factorial] at this
    linarith
  have hpi := Real.pi_gt_d6
  have hlogpi : (1.1447292 : ℝ) < Real.log Real.pi := by
    rw [Real.lt_log_iff_exp_lt hp, show (1.1447292 : ℝ) = 1 + 0.1447292 by norm_num, Real.exp_add]
    have := mul_le_mul he1.le hE (Real.exp_pos _).le (by norm_num)
    norm_num at this ⊢
    linarith
  unfold criticalBinaryExponent
  rw [Real.logb, Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_mul (by norm_num) hp.ne']
  rw [show (0.6044 : ℝ) < 1 / 2 * ((Real.log 2 + Real.log Real.pi - 1) / Real.log 2) ↔
      0.6044 * (2 * Real.log 2) < Real.log 2 + Real.log Real.pi - 1 by
    rw [show 1 / 2 * ((Real.log 2 + Real.log Real.pi - 1) / Real.log 2) = (Real.log 2 + Real.log Real.pi - 1) / (2 * Real.log 2) by field_simp]
    exact lt_div_iff₀ (by positivity)]
  linarith

