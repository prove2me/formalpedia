-- Prove2me | solution 1 for CohnElkies.saddleSourcePositiveShellThirdMoment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/11c2e598-b404-43fb-b2cc-0c2836b2ee41

import Mathlib
import Definitions.Def_SpherePacking

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
    {ε : ℝ} (hε : 0 < ε) (δ : ℝ) :
    0 ≤ upperPositiveShellThirdMoment ε δ := by
  have hB : 0 ≤ shellLocation ε := by
    unfold shellLocation
    positivity
  unfold upperPositiveShellThirdMoment
  apply intervalIntegral.integral_nonneg (by linarith)
  intro a ha
  have ha : 0 ≤ a := hB.trans ha.1
  have hdensity : 0 ≤ positiveShellDensity ε a := by
    unfold positiveShellDensity
    exact div_nonneg (shellWeight_pos ε).le
      (Real.cosh_pos a).le
  exact mul_nonneg
    (mul_nonneg hdensity (pow_nonneg ha 3))
    (Real.cosh_pos _).le
end CohnElkies
