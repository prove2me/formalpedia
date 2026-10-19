-- Prove2me | solution 1 for CohnElkies.saddleTaylorContour_gammaArgument
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/df23721f-c752-4b8a-8918-f2d20c887739

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (N : ℕ) (s : ℝ) :
    (((saddleTaylorContour N : ℂ) +
      (s : ℂ) * Complex.I) / 2) =
      upperNegativeHalfGammaArgument N (-s) := by
  unfold saddleTaylorContour upperNegativeHalfGammaArgument
  push_cast
  ring
end CohnElkies
