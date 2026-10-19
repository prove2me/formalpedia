-- Prove2me | solution 1 for CohnElkies.halfIntegerGammaFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/44479a2d-20dc-41b1-a6e6-abd4649e3045

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution (j : ℕ) (y : ℝ) :
    (j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2 ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  norm_num at hre
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith
end CohnElkies
