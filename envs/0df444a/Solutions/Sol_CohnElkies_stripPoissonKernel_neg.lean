-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/85c31642-8046-46fd-9896-080b599e35b5

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
theorem _root_.solution (σ T : ℝ) :
    stripPoissonKernel σ (-T) = stripPoissonKernel σ T := by
  unfold stripPoissonKernel
  have hneg : Real.pi * (-T) / 2 = -(Real.pi * T / 2) := by ring
  rw [hneg, Real.cosh_neg]
end CohnElkies
