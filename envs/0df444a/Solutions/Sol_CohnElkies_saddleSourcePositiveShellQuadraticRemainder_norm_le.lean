-- Prove2me | solution 1 for CohnElkies.saddleSourcePositiveShellQuadraticRemainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/762c97c2-23bf-41a3-9813-c17c93e4a312

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceWeightedCosineQuadraticRemainder_norm_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε)
    (u T : ℝ) :
    ‖∫ a in shellLocation ε..shellLocation ε + 1,
        (positiveShellDensity ε a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T‖ ≤
      (|T| ^ 3 / 6) *
        upperPositiveShellThirdMoment ε (u - 1) := by
  have hB : 0 ≤ shellLocation ε := by
    unfold shellLocation
    positivity
  have hbound :=
    saddleSourceWeightedCosineQuadraticRemainder_norm_le
      (positiveShellDensity ε)
      (show shellLocation ε ≤ shellLocation ε + 1 by linarith)
      hB
      (positiveShellDensity_continuous ε).continuousOn
      (fun a ha => by
        unfold positiveShellDensity
        exact div_nonneg (shellWeight_pos ε).le
          (Real.cosh_pos a).le)
      u T
  convert! hbound using 1
  unfold upperPositiveShellThirdMoment
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  ring_nf
end CohnElkies
