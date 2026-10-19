-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalInverseRootAngularL2_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/f86bfc79-fa03-45aa-8c90-9500b9166b92

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_complexLp_norm_sq_eq_integral

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
    (k : ℕ) (t : ℝ) {J : ℝ}
    (hJ : ∀ q : LogTorus n,
      |jointSourceTorusAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ J) :
    ‖(momentWeakHolomorphicStrictJointPhysicalInverseRoot_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hJ).toLp
        (angularSourceFreeInverseRootGradientField
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)
          (momentWeakHolomorphicStrictJointPhysicalCenteredCover
            K F htransport p ε k t))‖ ^ 2 =
    ∫ q : LogTorus n,
      momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε k t q
        ∂(angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) := by
  rw [complexLp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards
    [(momentWeakHolomorphicStrictJointPhysicalInverseRoot_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hJ).coeFn_toLp]
      with q hq
  rw [hq]
  exact
    (momentWeakHolomorphicStrictJointPhysicalRowEnergy_eq_inverseRoot_norm_sq
      K F htransport p ε hε₀ hε₁ k t q).symm
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
