-- Prove2me | solution 2 for CohnElkies.saddle_integral_exp_neg_mul_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:04:33.592855+00:00
-- url     : https://prove2.me/submissions/7719c511-86dd-4c1d-b307-10fc879a58c1

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology


theorem solution
    {a : ℝ} (ha : 0 < a) :
    (∫ T : ℝ, Real.exp (-a * |T|)) = 2 / a := by
  rw [integral_comp_abs (f := fun T => Real.exp (-a * T)),
    integral_exp_mul_Ioi (by linarith : -a < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

