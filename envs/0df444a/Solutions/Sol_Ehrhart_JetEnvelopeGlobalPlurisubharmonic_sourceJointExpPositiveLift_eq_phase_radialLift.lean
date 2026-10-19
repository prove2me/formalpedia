-- Prove2me | solution 1 for Ehrhart.JetEnvelopeGlobalPlurisubharmonic.sourceJointExpPositiveLift_eq_phase_radialLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/83033515-cdb9-4d7b-b720-39bb1706cdd8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeGlobalPlurisubharmonic
open Set Filter MeasureTheory Metric
open ActualJetUpperEnvelope JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace Ehrhart.JetEnvelopeGlobalPlurisubharmonic
theorem _root_.solution
    {n : ℕ}
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    sourceJointExpPositiveLift q hq =
      sourceJointPhaseHomeomorph
        (Complex.exp ((q.2.im : ℂ) * Complex.I))
        (sourceJointAuxiliaryPhase_norm q.2)
        (sourcePositiveJointTimePoint q.1
          (sourceJointCoverTime q) hq) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change
      Complex.exp q.2 =
        Complex.exp ((q.2.im : ℂ) * Complex.I) *
          (Real.exp (sourceJointCoverTime q / 2) : ℂ)
    rw [sourceJointCoverTime,
      show 2 * q.2.re / 2 = q.2.re by ring,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp [add_comm]
end Ehrhart.JetEnvelopeGlobalPlurisubharmonic
