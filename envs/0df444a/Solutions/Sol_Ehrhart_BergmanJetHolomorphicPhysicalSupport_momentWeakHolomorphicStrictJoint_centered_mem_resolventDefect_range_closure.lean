-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalSupport.momentWeakHolomorphicStrictJoint_centered_mem_resolventDefect_range_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/fa658c7f-5665-4b93-840f-c9f8dece6c46

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularResolventDefect_sourceFreeAngularCentered_mem_resolventDefect_range_closure
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalSupport_momentWeakHolomorphicStrictJointTorusWeight_le_support_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetHolomorphicPhysicalSupport
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert BergmanDiagonalBasisIndependence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative JetEnvelopeTrueRadialMollifier
open EnvelopeSmoothing EnvelopeGeneralTorusDescent RadialPartitionBounds MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentWeakBergman BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetSpatialSmoothing
open BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicStrictSchur
open BergmanJetHolomorphicPhysicalMeasure WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology ContDiff Convolution
namespace Ehrhart.BergmanJetHolomorphicPhysicalSupport
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (f : angularWeightedScalarL2
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t))
    (hf :
      (∫ q : LogTorus n,
        f q ∂(angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t))) = 0) :
    f ∈
      ((ContinuousLinearMap.id ℂ
        (angularWeightedScalarL2
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) -
        angularWeakScalarResolventCLM
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)).range).topologicalClosure := by
  let : IsFiniteMeasure
      (angularWeightedTorusMeasure
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) :=
    momentWeakHolomorphicStrictJointWeightedMeasure_isFinite
      K F htransport p k t hε₀ hε₁
  exact sourceFreeAngularCentered_mem_resolventDefect_range_closure
    K
    (continuous_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t)
    (momentWeakHolomorphicStrictJointTorusWeight_le_support_add
      K F htransport p k t hε₀.le hε₁)
    f hf
end Ehrhart.BergmanJetHolomorphicPhysicalSupport
