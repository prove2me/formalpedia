-- Prove2me | solution 1 for Ehrhart.JetEnvelopeGlobalPlurisubharmonic.jointLogTime_sourceJointExpPositiveLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/0e98e209-6eb3-4327-b36a-3d02a3a41cf0

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
    jointLogTime (sourceJointExpPositiveLift q hq) =
      sourceJointCoverTime q := by
  unfold jointLogTime sourceJointExpPositiveLift
  rw [normSq_sourceJointCoverExp, Real.log_exp]
end Ehrhart.JetEnvelopeGlobalPlurisubharmonic
