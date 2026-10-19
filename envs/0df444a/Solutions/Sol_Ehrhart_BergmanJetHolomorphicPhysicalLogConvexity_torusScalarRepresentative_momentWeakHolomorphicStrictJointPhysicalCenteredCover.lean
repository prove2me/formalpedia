-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.torusScalarRepresentative_momentWeakHolomorphicStrictJointPhysicalCenteredCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/54cbfd30-d3c7-4eb2-8ba5-3c7e7f025065

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_jointSourceTorusVelocity_eq_cover

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
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) :
    torusScalarRepresentative
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t) q =
    momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
      K F htransport p ε k t q := by
  unfold torusScalarRepresentative
    momentWeakHolomorphicStrictJointPhysicalCenteredCover
    momentWeakHolomorphicStrictJointPhysicalMixedCover
    momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
  rw [jointSourceTorusVelocity_eq_cover]
  change
    (jointSourceCoverVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (sourceTorusCoverPoint q, (t / 2 : ℂ)) : ℂ) - _ =
    ((jointSourceCoverVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) -
      sourceProbabilityMean
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k) t
        (jointSourceTorusVelocity
          (momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k) t) : ℝ) : ℂ)
  simp [sourceJointTimeEmbedding]
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
