-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_mem_resolventDefect_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/e03b056c-f994-465e-b5c7-1c1f62a12c1e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalSupport_momentWeakHolomorphicStrictJoint_centered_mem_resolventDefect_range_closure
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_integral_eq_zero

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
    (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB).toLp
        (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
          K F htransport p ε k t) ∈
      ((ContinuousLinearMap.id ℂ
        (angularWeightedScalarL2
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) -
        angularWeakScalarResolventCLM
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)).range).topologicalClosure := by
  apply momentWeakHolomorphicStrictJoint_centered_mem_resolventDefect_range_closure
    K F htransport p k t hε₀ hε₁
  rw [← momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_integral_eq_zero
    K F htransport p ε hε₀ hε₁ k t hB]
  exact integral_congr_ae
    (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB).coeFn_toLp
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
