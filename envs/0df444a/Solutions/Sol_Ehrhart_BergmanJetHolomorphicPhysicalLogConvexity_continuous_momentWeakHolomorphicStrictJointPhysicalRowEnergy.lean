-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.continuous_momentWeakHolomorphicStrictJointPhysicalRowEnergy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/6b01f9f0-5134-4a41-8bce-36bfba9fc15d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (k : ℕ) (t : ℝ) :
    Continuous
      (momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε k t) := by
  have hroot := continuous_angularSourceFreeInverseRootGradientField
    ((contDiff_infty.mp
      (contDiff_angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t)) 2)
    (angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
      K F htransport p ε hε₀ hε₁ k t)
    (contDiff_momentWeakHolomorphicStrictJointPhysicalCenteredCover
      K F htransport p ε k t)
    (momentWeakHolomorphicStrictJointPhysicalCenteredCover_periodic
      K F htransport p ε k t)
  have heq :
      momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε k t =
      fun q : LogTorus n =>
        ‖angularSourceFreeInverseRootGradientField
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)
          (momentWeakHolomorphicStrictJointPhysicalCenteredCover
            K F htransport p ε k t) q‖ ^ 2 := by
    funext q
    exact
      momentWeakHolomorphicStrictJointPhysicalRowEnergy_eq_inverseRoot_norm_sq
        K F htransport p ε hε₀ hε₁ k t q
  rw [heq]
  exact hroot.norm.pow 2
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
