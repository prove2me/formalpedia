-- Prove2me | solution 2 for CohnElkies.positiveShellDamping_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:11:19.7859+00:00
-- url     : https://prove2.me/submissions/e65ee986-689e-4cda-ba42-4a0af79f5fd9

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ε ℓ δ T : ℝ}
    (hℓ : 0 ≤ ℓ) :
    0 ≤ positiveShellDamping ε ℓ δ T := by
  unfold positiveShellDamping
  apply mul_nonneg hℓ
  apply intervalIntegral.integral_nonneg (by linarith)
  intro a _
  unfold positiveShellDensity shellWeight
  have h1 : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
  have h2 := Real.cosh_pos a
  have h3 := Real.cosh_pos ((1 + δ) * a)
  positivity

