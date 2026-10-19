-- Prove2me | solution 1 for CohnElkies.upperShortShellDamping_neg_frequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/3afa4519-4b0a-45c7-9936-6188a61710d0

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
    (ε ℓ δ T : ℝ) :
    upperShortShellDamping ε ℓ δ (-T) =
      upperShortShellDamping ε ℓ δ T := by
  unfold upperShortShellDamping
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  change
    (-shortShellDensity ε a) *
        Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * (-T))) =
      (-shortShellDensity ε a) *
        Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * T))
  rw [show a * (-T) = -(a * T) by ring, Real.cos_neg]
end CohnElkies
