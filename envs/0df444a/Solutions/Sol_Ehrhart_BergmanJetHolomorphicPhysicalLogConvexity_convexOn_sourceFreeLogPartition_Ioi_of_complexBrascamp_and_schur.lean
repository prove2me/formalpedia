-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.convexOn_sourceFreeLogPartition_Ioi_of_complexBrascamp_and_schur
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/dd85c85c-423b-450c-96b7-bc4b90499562

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_hasDerivAt_sourceFreeLogPartition_of_majorant
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_hasDerivAt_sourceFreeLogSlope_of_majorant
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_zero_lt_of_mem_positiveHalfBall
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFreeLogCurvature_nonneg_of_complexBrascamp_and_schur

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
    (a f j E : ℝ → LogTorus n → ℝ)
    (ha : ∀ t : ℝ, Continuous (a t))
    (hf : ∀ t : ℝ, Continuous (f t))
    (hj : ∀ t : ℝ, Continuous (j t))
    (hderiv : ∀ (t : ℝ) (q : LogTorus n),
      HasDerivAt (fun u : ℝ => a u q) (f t q) t)
    (hfderiv : ∀ (t : ℝ) (q : LogTorus n),
      HasDerivAt (fun u : ℝ => f u q) (j t q) t)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ (t : ℝ), 0 < t → ∀ q : LogTorus n,
      sourceTimeDensity a t q ≤ M q)
    (hpart : ∀ (t : ℝ), 0 < t → 0 < sourcePartition a t)
    (hprob : ∀ (t : ℝ), 0 < t →
      IsProbabilityMeasure (sourceProbability a t))
    (hfbound : ∀ (t : ℝ), 0 < t → ∃ B : ℝ,
      ∀ u ∈ Metric.ball t (t / 2),
        ∀ q : LogTorus n, |f u q| ≤ B)
    (hjbound : ∀ (t : ℝ), 0 < t → ∃ J : ℝ,
      ∀ u ∈ Metric.ball t (t / 2),
        ∀ q : LogTorus n, |j u q| ≤ J)
    (hEint : ∀ (t : ℝ), 0 < t →
      Integrable (E t) (sourceProbability a t))
    (hcomplexBrascamp : ∀ (t : ℝ), 0 < t →
      sourceProbabilityVariance a t (f t) ≤
        sourceProbabilityMean a t (E t))
    (hschur : ∀ (t : ℝ), 0 < t →
      ∀ q : LogTorus n, E t q ≤ j t q) :
    ConvexOn ℝ (Set.Ioi 0) (sourceLogPartition a) := by
  have hfirst : ∀ (t : ℝ), 0 < t →
      HasDerivAt (sourceLogPartition a) (sourceLogSlope a f t) t := by
    intro t ht
    obtain ⟨B, hB⟩ := hfbound t ht
    apply hasDerivAt_sourceFreeLogPartition_of_majorant
      a f (Metric.ball_mem_nhds t (half_pos ht))
      ha hf hderiv M hM
      (fun u hu q => hdom u
        (zero_lt_of_mem_positiveHalfBall ht hu) q)
      hB (hpart t ht)
  have hsecond : ∀ (t : ℝ), 0 < t →
      HasDerivAt (sourceLogSlope a f)
        (sourceAccelerationMoment a j t / sourcePartition a t -
          sourceMomentVariance a f t) t := by
    intro t ht
    obtain ⟨B, hB⟩ := hfbound t ht
    obtain ⟨J, hJ⟩ := hjbound t ht
    exact hasDerivAt_sourceFreeLogSlope_of_majorant
      a f j (Metric.ball_mem_nhds t (half_pos ht))
      ha hf hj hderiv hfderiv M hM
      (fun u hu q => hdom u
        (zero_lt_of_mem_positiveHalfBall ht hu) q)
      hB hJ (hpart t ht)
  have hcurvature : ∀ (t : ℝ), 0 < t →
      0 ≤ sourceAccelerationMoment a j t / sourcePartition a t -
        sourceMomentVariance a f t := by
    intro t ht
    obtain ⟨B, hB⟩ := hfbound t ht
    obtain ⟨J, hJ⟩ := hjbound t ht
    have htball : t ∈ Metric.ball t (t / 2) :=
      Metric.mem_ball_self (half_pos ht)
    exact sourceFreeLogCurvature_nonneg_of_complexBrascamp_and_schur
      a f j (E t) t B J
      (ha t) (hf t) (hj t) (hpart t ht) (hprob t ht)
      (hB t htball) (hJ t htball)
      (hEint t ht) (hcomplexBrascamp t ht) (hschur t ht)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi (0 : ℝ))
    (fun t ht => (hfirst t ht).continuousAt.continuousWithinAt)
    (f' := sourceLogSlope a f)
    (f'' := fun t =>
      sourceAccelerationMoment a j t / sourcePartition a t -
        sourceMomentVariance a f t)
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    exact (hfirst t ht').hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    exact (hsecond t ht').hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    exact hcurvature t ht'
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
