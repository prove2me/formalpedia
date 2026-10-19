-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.momentWeakJointCoverFiniteGeodesic_le_time_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/3cfca9d4-75e3-4cdf-af05-ca2786e4cb23

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (p : LogSpace n) (k : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteGeodesic
        K F htransport p k q ≤
      momentWeakJointCoverFiniteGeodesic
        K F htransport p k
          (q + momentWeakJointRealTimeShift n h) := by
  have htime :
      sourceJointCoverTime q ≤ sourceJointCoverTime q + h := by
    linarith
  have hmono := monotone_momentJetGeodesic
    K (Nat.zero_lt_succ k) F htransport p q.1
      (Nat.floor (BodyScale.canonicalScale K *
        ((k + 1 : ℕ) : ℝ))) htime
  unfold momentWeakJointCoverFiniteGeodesic
  rw [show
      (q + momentWeakJointRealTimeShift n h).1 = q.1 by
        simp [momentWeakJointRealTimeShift],
    sourceJointCoverTime_add_momentWeakJointRealTimeShift]
  exact hmono
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
