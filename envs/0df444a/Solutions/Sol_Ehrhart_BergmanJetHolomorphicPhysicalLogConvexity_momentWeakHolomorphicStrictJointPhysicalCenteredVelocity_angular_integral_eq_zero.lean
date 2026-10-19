-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_integral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/31a39e3d-a7b9-47d3-8edd-4f0d1febde60

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointPartition_pos
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_probability_integral_eq_zero

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
        ∂(angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t))) = 0 := by
  let a : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k
  let Z : ℝ := sourcePartition a t
  have hZ : 0 < Z :=
    momentWeakHolomorphicStrictJointPartition_pos
      K F htransport p k t hε₀ hε₁
  have hzero :=
    momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_probability_integral_eq_zero
      K F htransport p ε hε₀ hε₁ k t hB
  rw [momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
    K F htransport p k t hε₀ hε₁,
    integral_smul_measure] at hzero
  have hfactor : ((ENNReal.ofReal Z)⁻¹).toReal ≠ 0 := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
    exact inv_ne_zero hZ.ne'
  exact (smul_eq_zero.mp hzero).resolve_left hfactor
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
