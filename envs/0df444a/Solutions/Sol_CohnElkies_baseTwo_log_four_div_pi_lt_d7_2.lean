-- Prove2me | solution 2 for CohnElkies.baseTwo_log_four_div_pi_lt_d7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:31:33.336552+00:00
-- url     : https://prove2.me/submissions/51b29550-8843-45cf-b6ed-eeee92636115

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
    Real.log (4 / Real.pi) < (0.2415647 : ℝ) := by
  have hpi := Real.pi_gt_d20
  have hpi4 := Real.pi_lt_four
  have hx0 : 0 < 1 - Real.pi / 4 := by linarith
  have hx1 : 1 - Real.pi / 4 ≤ (0.21460184 : ℝ) := by norm_num at hpi ⊢; linarith
  have habs : |1 - Real.pi / 4| < 1 := by rw [abs_of_pos hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 10
  have hlog : Real.log (4 / Real.pi) = -Real.log (1 - (1 - Real.pi / 4)) := by
    rw [sub_sub_cancel, ← Real.log_inv, inv_div]
  rw [hlog]
  rw [abs_of_pos hx0] at h
  have hS : (∑ i ∈ Finset.range 10, (1 - Real.pi / 4) ^ (i + 1) / ((i : ℝ) + 1)) ≤
      ∑ i ∈ Finset.range 10, (0.21460184 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro i _
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ hx0.le hx1 _
  have hT : (1 - Real.pi / 4) ^ (10 + 1) / (1 - (1 - Real.pi / 4)) ≤
      (0.21460184 : ℝ) ^ (10 + 1) / (1 - 0.21460184) := by
    apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hx0.le hx1 _) (by norm_num) (by linarith)
  have hnum : (∑ i ∈ Finset.range 10, (0.21460184 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) +
      (0.21460184 : ℝ) ^ (10 + 1) / (1 - 0.21460184) < 0.2415647 := by
    norm_num [Finset.sum_range_succ]
  have h2 := (abs_le.mp h).1
  linarith

