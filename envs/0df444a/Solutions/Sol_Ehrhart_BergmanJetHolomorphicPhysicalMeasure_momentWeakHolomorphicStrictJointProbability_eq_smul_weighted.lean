-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalMeasure.momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/c030aa7e-5a90-4c10-a8e6-22bda157dbc0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointPartition_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetHolomorphicPhysicalMeasure
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence MatrixTorusBochnerBridge
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentMoserTrudinger
open BergmanJetEnvelopePlurisubharmonic BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetStrictRadialRegularizer
open BergmanJetJointHolomorphicStrictSchur JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeRightDerivative JetEnvelopeTrueRadialMollifier EnvelopeSmoothing
open EnvelopeGeneralTorusDescent RadialPartitionBounds LogPartitionConvexity WeightedTorusDolbeault
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology ContDiff Convolution
namespace Ehrhart.BergmanJetHolomorphicPhysicalMeasure
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    sourceProbability
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t =
      (ENNReal.ofReal
        (sourcePartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k) t))⁻¹ •
        angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t) := by
  let a : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k
  have hpart : 0 < sourcePartition a t :=
    momentWeakHolomorphicStrictJointPartition_pos
      K F htransport p k t hε₀ hε₁
  have hmeas : Measurable
      (fun q : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity (a t) q)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity
        (continuous_momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)).measurable
  change sourceProbability a t =
    (ENNReal.ofReal (sourcePartition a t))⁻¹ •
      angularWeightedTorusMeasure (a t)
  unfold sourceProbability angularWeightedTorusMeasure
  rw [← MeasureTheory.withDensity_smul _ hmeas]
  congr 1
  funext q
  change ENNReal.ofReal
    (Real.exp (-a t q) / sourcePartition a t) =
      (ENNReal.ofReal (sourcePartition a t))⁻¹ *
        ENNReal.ofReal (Real.exp (-a t q))
  rw [ENNReal.ofReal_div_of_pos hpart]
  simp [div_eq_mul_inv, mul_comm]
end Ehrhart.BergmanJetHolomorphicPhysicalMeasure
