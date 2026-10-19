-- Prove2me | solution 1 for CohnElkies.complexGamma_differentiableOn_positiveHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/1e2a0737-e7a2-4b1e-921b-a90ae8384df1

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
theorem _root_.solution :
    DifferentiableOn ℂ Complex.Gamma
      {z : ℂ | 0 < z.re} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply Complex.differentiableAt_Gamma
  intro n hn
  have hre := congrArg Complex.re hn
  have hnreal : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  simp at hre
  change 0 < z.re at hz
  linarith
end CohnElkies
