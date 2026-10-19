-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalMeasure.momentWeakHolomorphicStrictJointProbability_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/1958061d-7a53-4d15-838c-73f99a0b8c46

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
        K F htransport p ε k) t Set.univ = 1 := by
  let a : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k
  have hpart : 0 < sourcePartition a t :=
    momentWeakHolomorphicStrictJointPartition_pos
      K F htransport p k t hε₀ hε₁
  have hraw : Integrable
      (sourceTimeDensity a t)
      (sourceTorusBaseMeasure n) :=
    integrable_exp_neg_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p k t hε₀ hε₁
  have hnorm : Integrable
      (sourceNormalizedDensity a t)
      (sourceTorusBaseMeasure n) := by
    exact hraw.div_const _
  change sourceProbability a t Set.univ = 1
  unfold sourceProbability
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hnorm
    (Filter.Eventually.of_forall fun q =>
      (div_pos (Real.exp_pos _) hpart).le)]
  change
    ENNReal.ofReal
      (∫ q : LogTorus n,
        sourceTimeDensity a t q / sourcePartition a t
          ∂(sourceTorusBaseMeasure n)) = 1
  rw [MeasureTheory.integral_div]
  change ENNReal.ofReal
    (sourcePartition a t / sourcePartition a t) = 1
  rw [div_self hpart.ne']
  exact ENNReal.ofReal_one
end Ehrhart.BergmanJetHolomorphicPhysicalMeasure
