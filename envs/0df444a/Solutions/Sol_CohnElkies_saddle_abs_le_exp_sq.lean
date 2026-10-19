-- Prove2me | solution 1 for CohnElkies.saddle_abs_le_exp_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:16:30.63806+00:00
-- url     : https://prove2.me/submissions/6ff0bd3f-5ed4-4e5a-b9ab-cd9607bc02e5

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


theorem solution (T : ℝ) :
    |T| ≤ Real.exp (T ^ 2) := by
  have h1 : |T| ≤ T ^ 2 + 1 := by nlinarith [abs_nonneg T, sq_abs T]
  linarith [Real.add_one_le_exp (T ^ 2)]

