-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_probability_integral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/dee873cc-a531-47fe-b427-e2c57066f0e3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointProbability_isProbability

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
    (k : ℕ) (t : ℝ)
    {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    (∫ q : LogTorus n,
      momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
        K F htransport p ε k t q
        ∂(sourceProbability
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k) t)) = 0 := by
  let a : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k
  let ν : Measure (LogTorus n) := sourceProbability a t
  let : IsProbabilityMeasure ν :=
    momentWeakHolomorphicStrictJointProbability_isProbability
      K F htransport p k t hε₀ hε₁
  let v : LogTorus n → ℝ :=
    jointSourceTorusVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) t
  let A : ℝ := sourceProbabilityMean a t v
  have hv : Integrable v ν := by
    apply Integrable.of_bound
      (continuous_jointSourceTorusVelocity
        ((contDiff_infty.mp
          (contDiff_momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k)) 2)
        (momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
          K F htransport p ε k) t).aestronglyMeasurable B
    filter_upwards [] with q
    exact hB q
  have hreal : (∫ q : LogTorus n, v q - A ∂ν) = 0 := by
    rw [integral_sub hv (integrable_const A)]
    simp [A, sourceProbabilityMean, ν]
  change (∫ q : LogTorus n, ((v q - A : ℝ) : ℂ) ∂ν) = 0
  rw [integral_complex_ofReal, hreal]
  norm_num
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
