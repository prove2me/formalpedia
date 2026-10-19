-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedClipped_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/19b805c3-3ef7-4384-9056-92283f2a72de

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_dimension_neg

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
    lowerGammaScaledCappedClipped d c D n (-Y) =
      lowerGammaScaledCappedClipped d c D n Y := by
  unfold lowerGammaScaledCappedClipped
  have hmul : ((d : ℝ) / 2) * (-Y) =
      -(((d : ℝ) / 2) * Y) := by ring
  rw [hmul,
    lowerGammaBoundaryCapped_dimension_neg
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y)]
end CohnElkies
