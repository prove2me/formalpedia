-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalVariance_eq_angular_L2_norm_sq_div_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/5b384a94-6e8e-42a8-b3c4-24ae0ae3b9ab

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointPartition_pos
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_momentWeakHolomorphicStrictJointPhysicalCenteredAngularL2_norm_sq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative LogPartitionConvexity
open JointHolomorphicLaurentFourierCompatibility EnvelopeSmoothing EnvelopeGeneralTorusDescent
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation WeightedTorusDolbeault
open WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph RadialSchurBlock TorusDeckGraphAdjoint
open RadialPhysicalInverseSquareRootEnergy MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicFullLeviSchur
open BergmanJetHolomorphicPhysicalMeasure BergmanJetHolomorphicPhysicalSupport
open BergmanJetJointHolomorphicPhysicalApproximation BergmanJetJointHolomorphicTimeDerivativeBounds
open TorusHomogeneousBrascampLieb
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff
namespace Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    sourceProbabilityVariance
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t) =
    (sourcePartition
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t)⁻¹ *
      ‖(momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
        K F htransport p ε hε₀ hε₁ k t hB).toLp
          (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
            K F htransport p ε k t)‖ ^ 2 := by
  have hpart := momentWeakHolomorphicStrictJointPartition_pos
    K F htransport p k t hε₀ hε₁
  unfold sourceProbabilityVariance
  rw [momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
    K F htransport p k t hε₀ hε₁,
    integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hpart.le,
    smul_eq_mul]
  rw [← momentWeakHolomorphicStrictJointPhysicalCenteredAngularL2_norm_sq
    K F htransport p ε hε₀ hε₁ k t hB]
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
