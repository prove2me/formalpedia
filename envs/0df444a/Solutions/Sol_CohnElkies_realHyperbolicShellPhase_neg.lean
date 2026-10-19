-- Prove2me | solution 1 for CohnElkies.realHyperbolicShellPhase_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/e7594a3d-2c01-4f28-bccb-cf09c06efaad

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution (ε u : ℝ) :
    realHyperbolicShellPhase ε (-u) =
      realHyperbolicShellPhase ε u := by
  unfold realHyperbolicShellPhase
  congr 1
  · apply intervalIntegral.integral_congr
    intro a _
    change
      shortShellDensity ε a * (Real.cosh (a * (-u)) - 1) =
        shortShellDensity ε a * (Real.cosh (a * u) - 1)
    rw [mul_neg, Real.cosh_neg]
  · apply intervalIntegral.integral_congr
    intro a _
    change
      positiveShellDensity ε a * (Real.cosh (a * (-u)) - 1) =
        positiveShellDensity ε a * (Real.cosh (a * u) - 1)
    rw [mul_neg, Real.cosh_neg]
end CohnElkies
