-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.convexOn_momentWeakHolomorphicStrictJointLogPartition_Ioi_of_timeBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/7684b967-f5f7-455a-a40b-3ccff48c53b0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_continuous_jointSourceTorusAcceleration
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_hasDerivAt_jointSourceTorusWeight
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_hasDerivAt_jointSourceTorusVelocity
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointPartition_pos
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointProbability_isProbability
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_integrable_momentWeakHolomorphicUniformDensityMajorant
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_exp_neg_momentWeakHolomorphicStrictJointTorusWeight_le_uniform
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFreeProbability_memLp_two_of_bound
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_convexOn_sourceFreeLogPartition_Ioi_of_complexBrascamp_and_schur
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_momentWeakHolomorphicStrictJointPhysicalRowEnergy_nonneg
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_momentWeakHolomorphicStrictJointPhysicalBrascamp
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_continuous_momentWeakHolomorphicStrictJointPhysicalRowEnergy

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
    (k : ℕ)
    (hvbound : ∀ (t : ℝ), 0 < t → ∃ B : ℝ,
      ∀ u ∈ Metric.ball t (t / 2),
        ∀ q : LogTorus n,
          |jointSourceTorusVelocity
            (momentWeakHolomorphicStrictJointCoverWeight
              K F htransport p ε k) u q| ≤ B)
    (hjbound : ∀ (t : ℝ), 0 < t → ∃ J : ℝ,
      ∀ u ∈ Metric.ball t (t / 2),
        ∀ q : LogTorus n,
          |jointSourceTorusAcceleration
            (momentWeakHolomorphicStrictJointCoverWeight
              K F htransport p ε k) u q| ≤ J) :
    ConvexOn ℝ (Set.Ioi 0)
      (sourceLogPartition
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k)) := by
  let G : SourceJointComplexCover n → ℝ :=
    momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k
  let a : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k
  let f : ℝ → LogTorus n → ℝ := jointSourceTorusVelocity G
  let j : ℝ → LogTorus n → ℝ := jointSourceTorusAcceleration G
  let E : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointPhysicalRowEnergy
      K F htransport p ε k
  have hG : ContDiff ℝ 2 G :=
    (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2
  have hGp : ∀ d : Fin n → ℤ,
      Function.Periodic G (imaginaryShift d, (0 : ℂ)) :=
    momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
      K F htransport p ε k
  change ConvexOn ℝ (Set.Ioi 0) (sourceLogPartition a)
  apply convexOn_sourceFreeLogPartition_Ioi_of_complexBrascamp_and_schur
    a f j E
    (fun t => continuous_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t)
    (fun t => continuous_jointSourceTorusVelocity hG hGp t)
    (fun t => continuous_jointSourceTorusAcceleration hG hGp t)
    (fun t q => hasDerivAt_jointSourceTorusWeight hG t q)
    (fun t q => hasDerivAt_jointSourceTorusVelocity hG t q)
    (momentWeakHolomorphicUniformDensityMajorant K F htransport)
    (integrable_momentWeakHolomorphicUniformDensityMajorant
      K F htransport)
  · intro t ht q
    exact exp_neg_momentWeakHolomorphicStrictJointTorusWeight_le_uniform
      K F htransport p k ht hε₀.le hε₁ q
  · intro t _
    exact momentWeakHolomorphicStrictJointPartition_pos
      K F htransport p k t hε₀ hε₁
  · intro t _
    exact momentWeakHolomorphicStrictJointProbability_isProbability
      K F htransport p k t hε₀ hε₁
  · exact hvbound
  · exact hjbound
  · intro t ht
    obtain ⟨J, hJ⟩ := hjbound t ht
    let : IsProbabilityMeasure (sourceProbability a t) :=
      momentWeakHolomorphicStrictJointProbability_isProbability
        K F htransport p k t hε₀ hε₁
    have htball : t ∈ Metric.ball t (t / 2) :=
      Metric.mem_ball_self (half_pos ht)
    have hpoint : ∀ q : LogTorus n,
        |E t q| ≤ J := by
      intro q
      rw [abs_of_nonneg
        (momentWeakHolomorphicStrictJointPhysicalRowEnergy_nonneg
          K F htransport p ε hε₀ hε₁ k t q)]
      exact
        (momentWeakHolomorphicStrictJointPhysicalRowEnergy_le_acceleration
          K F htransport p ε hε₀ hε₁ k t q).trans
          ((le_abs_self _).trans (hJ t htball q))
    exact (sourceFreeProbability_memLp_two_of_bound a (E t) t J
      (momentWeakHolomorphicStrictJointProbability_isProbability
        K F htransport p k t hε₀ hε₁)
      (continuous_momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε hε₀ hε₁ k t)
      hpoint).integrable (by norm_num)
  · intro t ht
    obtain ⟨B, hB⟩ := hvbound t ht
    obtain ⟨J, hJ⟩ := hjbound t ht
    have htball : t ∈ Metric.ball t (t / 2) :=
      Metric.mem_ball_self (half_pos ht)
    exact momentWeakHolomorphicStrictJointPhysicalBrascamp
      K F htransport p ε hε₀ hε₁ k t
      (hB t htball) (hJ t htball)
  · intro t _ q
    exact momentWeakHolomorphicStrictJointPhysicalRowEnergy_le_acceleration
      K F htransport p ε hε₀ hε₁ k t q
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
