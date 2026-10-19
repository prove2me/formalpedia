-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.sourceFree_integral_sourceProbability_velocity_sq_eq_secondMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/492db84b-59c9-466f-b455-562d5cb99a84

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFree_integral_sourceProbability_eq_density_integral

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
    (ha : Continuous (a t))
    (hpart : 0 < sourcePartition a t) :
    (∫ q : LogTorus n,
      f t q ^ 2 ∂(sourceProbability a t)) =
      sourceSecondMoment a f t / sourcePartition a t := by
  rw [sourceFree_integral_sourceProbability_eq_density_integral
    a t ha hpart (fun q => f t q ^ 2)]
  calc
    (∫ q : LogTorus n,
      f t q ^ 2 * sourceNormalizedDensity a t q
        ∂(sourceTorusBaseMeasure n)) =
      ∫ q : LogTorus n,
        (f t q ^ 2 * sourceTimeDensity a t q) /
          sourcePartition a t ∂(sourceTorusBaseMeasure n) := by
            apply integral_congr_ae
            filter_upwards [] with q
            simp [sourceNormalizedDensity, mul_div_assoc]
    _ = sourceSecondMoment a f t / sourcePartition a t := by
      rw [integral_div]
      rfl
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
