-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/e5650153-1486-4c5f-94bf-809443a483f3

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
namespace CohnElkies
theorem _root_.solution (x : ℝ) :
    upperImaginaryExp (-x) =
      starRingEnd ℂ (upperImaginaryExp x) := by
  apply Complex.ext <;>
    simp [upperImaginaryExp, Complex.exp_re, Complex.exp_im,
      Real.cos_neg, Real.sin_neg]
end CohnElkies
