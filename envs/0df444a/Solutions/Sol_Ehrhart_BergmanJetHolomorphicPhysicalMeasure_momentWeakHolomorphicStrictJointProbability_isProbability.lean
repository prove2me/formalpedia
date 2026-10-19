-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalMeasure.momentWeakHolomorphicStrictJointProbability_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/0d59141d-7b63-4bdf-9b01-cf0329aa0b3d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointProbability_univ

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
    IsProbabilityMeasure
      (sourceProbability
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k) t) :=
  ⟨momentWeakHolomorphicStrictJointProbability_univ
    K F htransport p k t hε₀ hε₁⟩
end Ehrhart.BergmanJetHolomorphicPhysicalMeasure
