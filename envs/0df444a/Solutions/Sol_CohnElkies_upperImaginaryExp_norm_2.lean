-- Prove2me | solution 2 for CohnElkies.upperImaginaryExp_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:58:22.927762+00:00
-- url     : https://prove2.me/submissions/004a1e8c-730d-42ea-95e8-ad205617b3f2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology


theorem solution (x : ℝ) :
    ‖upperImaginaryExp x‖ = 1 := by
  unfold upperImaginaryExp
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

