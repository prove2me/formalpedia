-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalCenteredAngularL2_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/acc2b7dc-da16-4a6f-8011-4d5268a454a2

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
    (k : ℕ) (t : ℝ) {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    ‖(momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB).toLp
        (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
          K F htransport p ε k t)‖ ^ 2 =
    ∫ q : LogTorus n,
      (jointSourceTorusVelocity
          (momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k) t q -
        sourceProbabilityMean
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k) t
          (jointSourceTorusVelocity
            (momentWeakHolomorphicStrictJointCoverWeight
              K F htransport p ε k) t)) ^ 2
        ∂(angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) := by
  rw [complexLp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards
    [(momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB).coeFn_toLp]
      with q hq
  rw [hq]
  unfold momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
