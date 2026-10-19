-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicConvexTransfer.exp_neg_canonicalScale_mul_le_momentBodyNormalizedPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/c6008535-e942-4ce3-bb55-1d333e801ccc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicConvexTransfer_exp_neg_canonicalScale_mul_volume_le_momentBodyPartition

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
    Real.exp (-(BodyScale.canonicalScale K * t)) ≤
      momentBodyNormalizedPartition K p t := by
  unfold momentBodyNormalizedPartition
  apply (le_div_iff₀ K.volume_pos).mpr
  exact exp_neg_canonicalScale_mul_volume_le_momentBodyPartition
    K p ht
end Ehrhart.BergmanJetJointHolomorphicConvexTransfer
