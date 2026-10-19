-- Prove2me | solution 1 for CohnElkies.stripSchwarzExponential_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/73491223-b3cf-43c7-8ff2-1191df4b764e

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (ℓ : ℝ) (z : ℂ) :
    Continuous (fun y : ℝ => stripSchwarzExponential ℓ z y) := by
  unfold stripSchwarzExponential
  fun_prop
end CohnElkies
