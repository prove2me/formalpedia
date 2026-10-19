-- Prove2me | solution 1 for CohnElkies.saddleSourcePositiveShellVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/4319c133-a21a-4687-93c3-4bb04ed410cc

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    (ε δ : ℝ) :
    0 ≤ upperPositiveShellVariance ε δ := by
  unfold upperPositiveShellVariance
  apply intervalIntegral.integral_nonneg
    (show shellLocation ε ≤ shellLocation ε + 1 by linarith)
  intro a ha
  unfold positiveShellDensity
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg (shellWeight_pos ε).le
        (Real.cosh_pos a).le)
      (sq_nonneg a))
    (Real.cosh_pos _).le
end CohnElkies
