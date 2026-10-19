-- Prove2me | solution 2 for CohnElkies.abs_exp_sub_one_le_abs_mul_exp_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:57:50.857226+00:00
-- url     : https://prove2.me/submissions/18c0b083-9616-44d7-aeb7-0f259eec3dd1

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


theorem solution (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  rcases le_total 0 t with ht | ht
  · have h1 := Real.add_one_le_exp (-t)
    have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    have h3 : 1 ≤ Real.exp t := Real.one_le_exp ht
    rw [abs_of_nonneg (by linarith : 0 ≤ Real.exp t - 1), abs_of_nonneg ht]
    nlinarith [Real.exp_pos t]
  · have h1 := Real.add_one_le_exp t
    have h3 : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr ht
    have h4 : 1 ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
    rw [abs_of_nonpos (by linarith : Real.exp t - 1 ≤ 0), abs_of_nonpos ht]
    nlinarith

