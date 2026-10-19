-- Prove2me | solution 2 for CohnElkies.tendsto_upper_log_cubic_gaussian_atTop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:11:23.545216+00:00
-- url     : https://prove2.me/submissions/57d90617-5228-4522-8779-bfb92c701a0a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution :
    Tendsto (fun x : ℝ =>
      (10 * Real.log x + x ^ 3) *
        Real.exp (-(x ^ 2) / 8))
      atTop (𝓝 (0 : ℝ)) := by
  have hy : Tendsto (fun x : ℝ => x ^ 2 / 8) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
  have h0 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hy).const_mul (704 : ℝ)
  rw [mul_zero] at h0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have := Real.log_nonneg hx
    positivity
  · filter_upwards [eventually_ge_atTop 1] with x hx
    simp only [Function.comp]
    have he : Real.exp (-(x ^ 2) / 8) = Real.exp (-(x ^ 2 / 8)) := by ring_nf
    rw [he]
    have hE := Real.exp_pos (-(x ^ 2 / 8))
    have hl : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hl0 := Real.log_nonneg hx
    have h1 : 10 * Real.log x + x ^ 3 ≤ 11 * x ^ 4 := by nlinarith [pow_le_pow_right₀ hx (show 1 ≤ 4 by norm_num), pow_le_pow_right₀ hx (show 3 ≤ 4 by norm_num)]
    have h2 : 704 * ((x ^ 2 / 8) ^ 2 * Real.exp (-(x ^ 2 / 8))) = 11 * x ^ 4 * Real.exp (-(x ^ 2 / 8)) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 hE.le

