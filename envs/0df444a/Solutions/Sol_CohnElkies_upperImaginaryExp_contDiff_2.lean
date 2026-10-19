-- Prove2me | solution 2 for CohnElkies.upperImaginaryExp_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:28.298988+00:00
-- url     : https://prove2.me/submissions/bcb72570-81dd-4a83-afeb-6a435a56ba5c

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


theorem solution :
    ContDiff ℝ (⊤ : WithTop ℕ∞) upperImaginaryExp := by
  unfold upperImaginaryExp
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

