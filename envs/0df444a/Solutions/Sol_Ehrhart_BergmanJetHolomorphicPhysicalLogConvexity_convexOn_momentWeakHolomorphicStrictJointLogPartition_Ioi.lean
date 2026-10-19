-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.convexOn_momentWeakHolomorphicStrictJointLogPartition_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/b804f623-790b-4a3b-a982-3b6bac187cd2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_exists_momentWeakHolomorphicStrictJointTorusVelocity_local_bound
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_exists_momentWeakHolomorphicStrictJointTorusAcceleration_local_bound
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_convexOn_momentWeakHolomorphicStrictJointLogPartition_Ioi_of_timeBounds

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
    (k : ℕ) :
    ConvexOn ℝ (Set.Ioi 0)
      (sourceLogPartition
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k)) := by
  apply
    convexOn_momentWeakHolomorphicStrictJointLogPartition_Ioi_of_timeBounds
      K F htransport p ε hε₀ hε₁ k
  · intro t _
    exact exists_momentWeakHolomorphicStrictJointTorusVelocity_local_bound
      K F htransport p ε hε₀.le hε₁ k t
  · intro t _
    exact exists_momentWeakHolomorphicStrictJointTorusAcceleration_local_bound
      K F htransport p ε hε₀.le hε₁ k t
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
