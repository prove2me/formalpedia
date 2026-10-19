-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.exists_momentWeakHolomorphicStrictJointTorusVelocity_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/50b6af93-ac1f-41ca-8052-aa79e87d5279

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_abs_momentWeakHolomorphicStrictJointTorusVelocity_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation BergmanJetEnvelopePlurisubharmonic
open BergmanJetUpperEnvelope BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative
open JetEnvelopeTrueRadialMollifier EnvelopeSmoothing EnvelopeGeneralTorusDescent
open RadialAccelerationBounds
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
attribute [local instance] Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) :
    ∃ B : ℝ, ∀ u ∈ Metric.ball t (t / 2),
      ∀ q : LogTorus n,
        |jointSourceTorusVelocity
          (momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k) u q| ≤ B := by
  refine ⟨BodyScale.canonicalScale K, ?_⟩
  intro u _ q
  exact abs_momentWeakHolomorphicStrictJointTorusVelocity_le
    K F htransport p ε hε₀ hε₁ k u q
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
