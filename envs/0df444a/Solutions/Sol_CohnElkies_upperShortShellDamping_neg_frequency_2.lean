-- Prove2me | solution 2 for CohnElkies.upperShortShellDamping_neg_frequency
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:21:50.937725+00:00
-- url     : https://prove2.me/submissions/41ba7239-a4e8-4cc1-9b95-a248af95fcdd

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


theorem solution
    (ε ℓ δ T : ℝ) :
    upperShortShellDamping ε ℓ δ (-T) =
      upperShortShellDamping ε ℓ δ T := by
  unfold upperShortShellDamping
  simp only [mul_neg, Real.cos_neg]

