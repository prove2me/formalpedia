-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalBrascamp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/bee7d2dd-81f2-4bc8-9e63-4bdb41269090

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointPartition_pos
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_angularSourceFreeBrascampLieb_of_mem_resolventDefect_closure
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_torusScalarRepresentative_momentWeakHolomorphicStrictJointPhysicalCenteredCover
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_mem_resolventDefect_closure
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_momentWeakHolomorphicStrictJointPhysicalVariance_eq_angular_L2_norm_sq_div_partition
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_momentWeakHolomorphicStrictJointPhysicalRowEnergy_probabilityMean_eq_angular_L2_norm_sq_div_partition

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
    {B J : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B)
    (hJ : ∀ q : LogTorus n,
      |jointSourceTorusAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ J) :
    sourceProbabilityVariance
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t) ≤
    sourceProbabilityMean
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε k t) := by
  let a : LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t
  let U : LogSpace n → ℂ :=
    momentWeakHolomorphicStrictJointPhysicalCenteredCover
      K F htransport p ε k t
  let hv :=
    momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB
  have hUeq : torusScalarRepresentative U =
      momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
        K F htransport p ε k t := by
    funext q
    exact
      torusScalarRepresentative_momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t q
  have hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a) := by
    rw [hUeq]
    exact hv
  let hr :=
    momentWeakHolomorphicStrictJointPhysicalInverseRoot_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hJ
  have hclosure :
      hu.toLp (torusScalarRepresentative U) ∈
        ((ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
          angularWeakScalarResolventCLM a).range).topologicalClosure := by
    simpa only [hUeq] using
      momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_mem_resolventDefect_closure
        K F htransport p ε hε₀ hε₁ k t hB
  have hnorm := angularSourceFreeBrascampLieb_of_mem_resolventDefect_closure
    (continuous_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t)
    ((contDiff_infty.mp
      (contDiff_angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t)) 3)
    (angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
      K F htransport p ε hε₀ hε₁ k t)
    (contDiff_momentWeakHolomorphicStrictJointPhysicalCenteredCover
      K F htransport p ε k t)
    (momentWeakHolomorphicStrictJointPhysicalCenteredCover_periodic
      K F htransport p ε k t)
    hu hr hclosure
  have hleft : hu.toLp (torusScalarRepresentative U) =
      hv.toLp
        (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
          K F htransport p ε k t) := by
    apply MemLp.toLp_congr
    filter_upwards [] with q
    exact congrFun hUeq q
  have hnorm' :
      ‖hv.toLp
        (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
          K F htransport p ε k t)‖ ≤
      ‖hr.toLp (angularSourceFreeInverseRootGradientField a U)‖ := by
    change
      ‖hu.toLp (torusScalarRepresentative U)‖ ≤
        ‖hr.toLp (angularSourceFreeInverseRootGradientField a U)‖
      at hnorm
    rw [hleft] at hnorm
    exact hnorm
  rw [momentWeakHolomorphicStrictJointPhysicalVariance_eq_angular_L2_norm_sq_div_partition
    K F htransport p ε hε₀ hε₁ k t hB,
    momentWeakHolomorphicStrictJointPhysicalRowEnergy_probabilityMean_eq_angular_L2_norm_sq_div_partition
      K F htransport p ε hε₀ hε₁ k t hJ]
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm')
    (inv_nonneg.mpr
      (momentWeakHolomorphicStrictJointPartition_pos
        K F htransport p k t hε₀ hε₁).le)
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
