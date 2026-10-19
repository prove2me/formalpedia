-- Prove2me | solution 2 for CohnElkies.upperImaginaryExp_neg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:42.430664+00:00
-- url     : https://prove2.me/submissions/d8379b36-4e15-4d73-973e-ce7278ff7994

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
    upperImaginaryExp (-x) =
      starRingEnd ℂ (upperImaginaryExp x) := by
  unfold upperImaginaryExp
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

