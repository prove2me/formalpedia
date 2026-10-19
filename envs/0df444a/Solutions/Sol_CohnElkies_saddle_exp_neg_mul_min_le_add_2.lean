-- Prove2me | solution 2 for CohnElkies.saddle_exp_neg_mul_min_le_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:37.023926+00:00
-- url     : https://prove2.me/submissions/47cad0cf-e180-4bcd-b011-cfccb263da95

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
    {a x y : ℝ} (ha : 0 ≤ a) :
    Real.exp (-a * min x y) ≤
      Real.exp (-a * x) + Real.exp (-a * y) := by
  rcases min_choice x y with h | h <;> rw [h]
  · have := Real.exp_pos (-a * y); linarith
  · have := Real.exp_pos (-a * x); linarith

