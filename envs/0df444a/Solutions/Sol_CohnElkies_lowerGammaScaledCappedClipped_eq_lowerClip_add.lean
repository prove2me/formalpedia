-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedClipped_eq_lowerClip_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/64cc6946-8976-49ff-9450-d3f50ebf0bb0

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    (d : ℕ) (c D n Y : ℝ) :
    lowerGammaScaledCappedClipped d c D n Y =
      lowerGammaScaledCappedLowerClip d c D n Y + n := by
  unfold lowerGammaScaledCappedClipped
    lowerGammaScaledCappedLowerClip
  have h := max_add_add_right
    (lowerGammaBoundaryCapped ((d : ℝ) / 2)
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))
    (-n) n
  simpa using! h
end CohnElkies
