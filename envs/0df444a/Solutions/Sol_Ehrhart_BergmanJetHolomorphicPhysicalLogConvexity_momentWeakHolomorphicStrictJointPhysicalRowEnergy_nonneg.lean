-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalRowEnergy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/cf8120fd-669a-4036-9f6e-e7e841bb7228

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_RadialSchurBlock_sourceComplexRowSchurEnergyDensity_nonneg

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
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    0 ≤ momentWeakHolomorphicStrictJointPhysicalRowEnergy
      K F htransport p ε k t q := by
  exact sourceComplexRowSchurEnergyDensity_nonneg
    (angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
      K F htransport p ε hε₀ hε₁ k t q)
    (momentWeakHolomorphicStrictJointPhysicalMixedRow
      K F htransport p ε k t q)
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
