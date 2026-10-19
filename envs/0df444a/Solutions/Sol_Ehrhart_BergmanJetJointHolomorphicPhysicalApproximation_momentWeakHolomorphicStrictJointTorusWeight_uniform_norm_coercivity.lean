-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.momentWeakHolomorphicStrictJointTorusWeight_uniform_norm_coercivity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/0de4050e-6547-47bc-9620-ecb50cee2180

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_momentTorusEnvelopeTimeSlice_le_holomorphicJointMollification

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentMoserTrudinger BergmanJetTorusEnvelope
open BergmanJetTorusCoercivity BergmanJetStrictRadialRegularizer
open BergmanJetJointEnvelopeRegularization BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open BergmanJetJointHolomorphicApproximation BergmanJetHolomorphicPhysicalMeasure
open JetEnvelopeRightDerivative JetEnvelopeSlopeConvergence JetEnvelopeGlobalPlurisubharmonic
open EnvelopeSmoothing EnvelopeGeneralTorusDescent LogPartitionConvexity
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
namespace Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) {t : ℝ} (ht : 0 < t)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (q : LogTorus n) :
    momentWeakHolomorphicUniformRadialRate K * ‖q.1‖ -
        momentWeakHolomorphicUniformCoercivityConstant
          K F htransport ≤
      momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t q := by
  let δ : ℝ :=
    (((momentCoerciveMonomialDegree K : ℕ) : ℝ)⁻¹)
  let s : ℝ := momentBodyStrictScale K
  let C : ℝ := momentTorusEnvelopeCoercivityConstant
    K F htransport
  let B : ℝ := max C 0
  let m : ℝ := min δ s
  have hnorm : 0 ≤ ‖q.1‖ := norm_nonneg _
  have hweak0 := momentTorusEnvelope_norm_coercivity
    K F htransport p q ht
  have hweak1 :=
    momentTorusEnvelopeTimeSlice_le_holomorphicJointMollification
      K F htransport p k ht q
  have hweak :
      δ * ‖q.1‖ - C ≤
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k
            (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by
    exact hweak0.trans hweak1
  have hrad :=
    momentWeakHolomorphicStrictRadialPotential_norm_lower K q.1
  have hmδ : m * ‖q.1‖ ≤ δ * ‖q.1‖ :=
    mul_le_mul_of_nonneg_right (min_le_left δ s) hnorm
  have hms : m * ‖q.1‖ ≤ s * ‖q.1‖ :=
    mul_le_mul_of_nonneg_right (min_le_right δ s) hnorm
  have hC : C ≤ B := le_max_left C 0
  have hB : 0 ≤ B := le_max_right C 0
  have hweight : 0 ≤ 1 - ε := sub_nonneg.mpr hε₁
  have hweak' := mul_le_mul_of_nonneg_left hweak hweight
  have hrad' := mul_le_mul_of_nonneg_left hrad hε₀
  have hmδ' := mul_le_mul_of_nonneg_left hmδ hweight
  have hms' := mul_le_mul_of_nonneg_left hms hε₀
  have hC' := mul_le_mul_of_nonneg_left hC hweight
  have hεB := mul_nonneg hε₀ hB
  rw [momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover]
  unfold momentWeakHolomorphicStrictJointCoverWeight
  have href :
      matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t).1 =
        momentBodyStrictRadialPotential K q.1 := by
    simp [sourceJointTimeEmbedding, sourceTorusCoverPoint,
      matrixSourceCoverPotential_logarithmicPoint]
  rw [href]
  change m * ‖q.1‖ - B ≤ _
  dsimp [δ, s, C, B, m] at *
  nlinarith
end Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
