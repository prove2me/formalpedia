-- Prove2me | solution 2 for CohnElkies.upperImaginaryExp_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:34.814499+00:00
-- url     : https://prove2.me/submissions/1565d945-fe2e-49bd-876a-e603eec084ff

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
    HasDerivAt upperImaginaryExp
      (Complex.I * upperImaginaryExp x) x := by
  unfold upperImaginaryExp
  have h : HasDerivAt (fun y : ℝ => Complex.I * (y : ℂ)) (Complex.I * 1) x :=
    (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul Complex.I |>.congr_deriv (by simp)
  have := h.cexp
  convert this using 1
  ring

