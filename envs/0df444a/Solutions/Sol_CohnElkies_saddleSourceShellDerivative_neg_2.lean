-- Prove2me | solution 2 for CohnElkies.saddleSourceShellDerivative_neg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:14.130897+00:00
-- url     : https://prove2.me/submissions/c247ace5-2212-42e6-9b59-692f4bde7616

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


theorem solution
    (ε u : ℝ) :
    saddleSourceShellDerivative ε (-u) =
      -saddleSourceShellDerivative ε u := by
  unfold saddleSourceShellDerivative
  simp only [neg_mul, Real.sinh_neg, mul_neg, intervalIntegral.integral_neg]
  ring

