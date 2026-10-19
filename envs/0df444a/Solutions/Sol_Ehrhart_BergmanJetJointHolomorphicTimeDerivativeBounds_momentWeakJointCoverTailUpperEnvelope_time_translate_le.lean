-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.momentWeakJointCoverTailUpperEnvelope_time_translate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/3017c35f-801c-4835-8f6d-2e551ba0705e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_upperRegularization_sourceJointCover_translate_le
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_momentWeakJointCoverTailSup_time_translate_le

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
    (p : LogSpace n) (r : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailUpperEnvelope
        K F htransport p r
          (q + momentWeakJointRealTimeShift n h) ≤
      momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q +
          BodyScale.canonicalScale K * h := by
  unfold momentWeakJointCoverTailUpperEnvelope
  exact upperRegularization_sourceJointCover_translate_le
    (momentWeakJointCoverTailSup K F htransport p r)
    (momentWeakJointCoverTailSup_localUpperBounds_nonempty
      K F htransport p r)
    (momentWeakJointRealTimeShift n h)
    (BodyScale.canonicalScale K * h)
    (momentWeakJointCoverTailSup_time_translate_le
      K F htransport p r hh) q
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
