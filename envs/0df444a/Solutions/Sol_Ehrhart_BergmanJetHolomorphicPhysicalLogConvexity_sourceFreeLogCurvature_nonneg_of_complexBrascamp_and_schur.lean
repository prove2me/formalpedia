-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.sourceFreeLogCurvature_nonneg_of_complexBrascamp_and_schur
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/7f52bc7c-d148-4e9b-8a61-100312fe68b1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFreeProbabilityMean_acceleration_eq_moment
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFreeProbability_memLp_two_of_bound
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFreeProbabilityVariance_eq_momentVariance

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
    (a f j : ℝ → LogTorus n → ℝ)
    (E : LogTorus n → ℝ)
    (t B J : ℝ)
    (ha : Continuous (a t))
    (hf : Continuous (f t))
    (hj : Continuous (j t))
    (hpart : 0 < sourcePartition a t)
    (hprob : IsProbabilityMeasure (sourceProbability a t))
    (hfbound : ∀ q : LogTorus n, |f t q| ≤ B)
    (hjbound : ∀ q : LogTorus n, |j t q| ≤ J)
    (hEint : Integrable E (sourceProbability a t))
    (hcomplexBrascamp :
      sourceProbabilityVariance a t (f t) ≤
        sourceProbabilityMean a t E)
    (hschur : ∀ q : LogTorus n, E q ≤ j t q) :
    0 ≤ sourceAccelerationMoment a j t / sourcePartition a t -
      sourceMomentVariance a f t := by
  let : IsProbabilityMeasure (sourceProbability a t) := hprob
  have hvelocity := sourceFreeProbability_memLp_two_of_bound
    a (f t) t B hprob hf hfbound
  have hacceleration := sourceFreeProbability_memLp_two_of_bound
    a (j t) t J hprob hj hjbound
  have hjint := hacceleration.integrable (by norm_num)
  apply sub_nonneg.mpr
  calc
    sourceMomentVariance a f t =
        sourceProbabilityVariance a t (f t) :=
      (sourceFreeProbabilityVariance_eq_momentVariance
        a f t ha hf hpart hprob hvelocity).symm
    _ ≤ sourceProbabilityMean a t E := hcomplexBrascamp
    _ ≤ sourceProbabilityMean a t (j t) :=
      MeasureTheory.integral_mono hEint hjint hschur
    _ = sourceAccelerationMoment a j t / sourcePartition a t :=
      sourceFreeProbabilityMean_acceleration_eq_moment
        a j t ha hpart
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
