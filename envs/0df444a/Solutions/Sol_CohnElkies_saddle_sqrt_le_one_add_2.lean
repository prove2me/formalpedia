-- Prove2me | solution 2 for CohnElkies.saddle_sqrt_le_one_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:50:57.32738+00:00
-- url     : https://prove2.me/submissions/a0b27bc2-9a0c-4589-85c2-7fd4ae30328e

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ 1 + x := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

