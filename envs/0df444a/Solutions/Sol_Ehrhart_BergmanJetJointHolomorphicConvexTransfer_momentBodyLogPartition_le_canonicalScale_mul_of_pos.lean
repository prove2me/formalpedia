-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicConvexTransfer.momentBodyLogPartition_le_canonicalScale_mul_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/40998bcd-70ea-452f-806a-04f8f295ec98

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPartitionEndpoint_momentBodyNormalizedPartition_pos
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicConvexTransfer_exp_neg_canonicalScale_mul_le_momentBodyNormalizedPartition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicConvexTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open MomentRegularity BergmanJetTorusEnvelope BergmanJetPartitionEndpoint
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicPhysicalApproximation
open JetEnvelopeSlopeConvergence LogPartitionConvexity
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetJointHolomorphicConvexTransfer
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    momentBodyLogPartition K p t ≤
      BodyScale.canonicalScale K * t := by
  have hlower :=
    exp_neg_canonicalScale_mul_le_momentBodyNormalizedPartition
      K p ht
  have hleft :
      0 < Real.exp (-(BodyScale.canonicalScale K * t)) :=
    Real.exp_pos _
  have hright := momentBodyNormalizedPartition_pos K p t
  have hlog := Real.strictMonoOn_log.monotoneOn hleft hright hlower
  rw [Real.log_exp] at hlog
  unfold momentBodyLogPartition
  linarith
end Ehrhart.BergmanJetJointHolomorphicConvexTransfer
