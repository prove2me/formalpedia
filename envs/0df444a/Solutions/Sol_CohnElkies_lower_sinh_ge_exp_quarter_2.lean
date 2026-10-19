-- Prove2me | solution 2 for CohnElkies.lower_sinh_ge_exp_quarter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:03:28.07583+00:00
-- url     : https://prove2.me/submissions/64b70990-e4e6-47f3-9d1d-e75621798240

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution
    {x : ℝ} (hx : 1 ≤ x) :
    Real.exp x / 4 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 := Real.add_one_le_exp x
  have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

