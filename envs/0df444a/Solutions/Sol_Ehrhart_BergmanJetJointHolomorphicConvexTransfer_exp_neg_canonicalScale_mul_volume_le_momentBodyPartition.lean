-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicConvexTransfer.exp_neg_canonicalScale_mul_volume_le_momentBodyPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/43bde7c5-d41f-477b-8ff6-b733d0bd5690

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusEnvelope_momentTorusEnvelopeTimeSlice_le_normalized_add

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
    Real.exp (-(BodyScale.canonicalScale K * t)) *
        normalizedVolume K.carrier ≤
      momentBodyPartition K p t := by
  have hzero :=
    integrable_exp_neg_momentBodyTorusWeight K p 0
  have htime :=
    integrable_exp_neg_momentBodyTorusWeight K p t
  calc
    Real.exp (-(BodyScale.canonicalScale K * t)) *
        normalizedVolume K.carrier =
      Real.exp (-(BodyScale.canonicalScale K * t)) *
        momentBodyPartition K p 0 := by
          rw [momentBodyPartition_zero]
    _ = ∫ q : LogTorus n,
          Real.exp (-(BodyScale.canonicalScale K * t)) *
            Real.exp (-momentBodyTorusWeight K p 0 q)
              ∂(sourceTorusBaseMeasure n) := by
          rw [momentBodyPartition_eq_integral,
            MeasureTheory.integral_const_mul]
    _ ≤ ∫ q : LogTorus n,
          Real.exp (-momentBodyTorusWeight K p t q)
            ∂(sourceTorusBaseMeasure n) := by
          apply MeasureTheory.integral_mono
            (hzero.const_mul
              (Real.exp
                (-(BodyScale.canonicalScale K * t))))
            htime
          intro q
          change
            Real.exp (-(BodyScale.canonicalScale K * t)) *
                Real.exp (-momentBodyTorusWeight K p 0 q) ≤
              Real.exp (-momentBodyTorusWeight K p t q)
          rw [← Real.exp_add,
            momentBodyTorusWeight_zero]
          apply Real.exp_le_exp.mpr
          have hupper := momentTorusEnvelopeTimeSlice_le_normalized_add
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K)
              p q ht
          change
            momentBodyTorusWeight K p t q ≤
              momentNormalizedPotential
                (momentBodyOptimizer K) q.1 +
                BodyScale.canonicalScale K * t at hupper
          linarith
    _ = momentBodyPartition K p t :=
      (momentBodyPartition_eq_integral K p t).symm
end Ehrhart.BergmanJetJointHolomorphicConvexTransfer
