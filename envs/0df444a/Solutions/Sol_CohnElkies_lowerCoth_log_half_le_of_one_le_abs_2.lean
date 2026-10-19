-- Prove2me | solution 2 for CohnElkies.lowerCoth_log_half_le_of_one_le_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:43.381088+00:00
-- url     : https://prove2.me/submissions/72759cd0-2ae8-4477-b783-bdef2fe9b0ef

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology


theorem solution
    {Y : ℝ} (hY : 1 ≤ |Y|) :
    (1 / 2 : ℝ) *
      Real.log (lowerCoth (Real.pi * |Y| / 2)) ≤
        (1 / 2 : ℝ) := by
  have hx : 3 / 2 ≤ Real.pi * |Y| / 2 := by nlinarith [Real.pi_gt_three]
  set x := Real.pi * |Y| / 2 with hxdef
  have hE := Real.exp_pos x
  have hF := Real.exp_pos (-x)
  have hEF : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hF2 : Real.exp (-2 * x) = Real.exp (-x) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hle : Real.exp (-2 * x) ≤ 1 / 4 := by
    have h1 : Real.exp (-2 * x) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith)
    have h2 : 4 ≤ Real.exp 3 := by have := Real.add_one_le_exp 3; linarith
    have h3 : Real.exp (-3) = (Real.exp 3)⁻¹ := by rw [Real.exp_neg]
    rw [h3] at h1
    have : (Real.exp 3)⁻¹ ≤ 1 / 4 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h2
    linarith
  rw [hF2] at hle
  have hEgt : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.2 (by linarith)
  have hc : lowerCoth x = (Real.exp x + Real.exp (-x)) / (Real.exp x - Real.exp (-x)) := by
    unfold lowerCoth; rw [Real.cosh_eq, Real.sinh_eq]; field_simp
  have hcpos : 0 < lowerCoth x := by rw [hc]; apply div_pos <;> linarith
  have hlog := Real.log_le_sub_one_of_pos hcpos
  have hb : lowerCoth x - 1 ≤ 4 * Real.exp (-x) ^ 2 := by
    rw [hc, div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith [mul_pos hF hF]
  linarith

