-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.sourceFreeProbabilityVariance_eq_momentVariance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/aac576a3-b20e-42d3-8d1d-445ba3f9f296

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFreeProbabilityMean_velocity_eq_logSlope
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFree_integral_sourceProbability_velocity_sq_eq_secondMoment

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
    {n : ℕ}
    (a f : ℝ → LogTorus n → ℝ) (t : ℝ)
    (ha : Continuous (a t)) (hf : Continuous (f t))
    (hpart : 0 < sourcePartition a t)
    (hprob : IsProbabilityMeasure (sourceProbability a t))
    (hmem : MemLp (f t) 2 (sourceProbability a t)) :
    sourceProbabilityVariance a t (f t) =
      sourceMomentVariance a f t := by
  let : IsProbabilityMeasure (sourceProbability a t) := hprob
  have hvariance := ProbabilityTheory.variance_eq_sub hmem
  rw [ProbabilityTheory.variance_eq_integral
    hf.measurable.aemeasurable] at hvariance
  have hreal :
      sourceProbabilityVariance a t (f t) =
        (∫ q : LogTorus n,
          f t q ^ 2 ∂(sourceProbability a t)) -
          (sourceProbabilityMean a t (f t)) ^ 2 := by
    simpa [sourceProbabilityVariance, sourceProbabilityMean,
      Pi.pow_apply] using hvariance
  rw [sourceFree_integral_sourceProbability_velocity_sq_eq_secondMoment
    a f t ha hpart,
    sourceFreeProbabilityMean_velocity_eq_logSlope
      a f t ha hpart] at hreal
  exact hreal
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
