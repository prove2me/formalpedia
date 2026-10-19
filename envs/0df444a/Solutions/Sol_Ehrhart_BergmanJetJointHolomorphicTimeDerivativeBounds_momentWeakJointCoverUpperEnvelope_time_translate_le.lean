-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.momentWeakJointCoverUpperEnvelope_time_translate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/28fd93e1-0301-45e5-a0d5-fbde204fac1d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_momentWeakJointCoverTailUpperEnvelope_time_translate_le

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
    (p : LogSpace n)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverUpperEnvelope
        K F htransport p
          (q + momentWeakJointRealTimeShift n h) ≤
      momentWeakJointCoverUpperEnvelope
        K F htransport p q +
          BodyScale.canonicalScale K * h := by
  have hright :
      Tendsto
        (fun r : ℕ =>
          momentWeakJointCoverTailUpperEnvelope
            K F htransport p r q +
              BodyScale.canonicalScale K * h)
        atTop
        (𝓝 (momentWeakJointCoverUpperEnvelope
          K F htransport p q +
            BodyScale.canonicalScale K * h)) :=
    (tendsto_momentWeakJointCoverTailUpperEnvelope
      K F htransport p q).add
        (tendsto_const_nhds :
          Tendsto
            (fun _ : ℕ => BodyScale.canonicalScale K * h)
            atTop
            (𝓝 (BodyScale.canonicalScale K * h)))
  apply le_of_tendsto_of_tendsto
    (tendsto_momentWeakJointCoverTailUpperEnvelope
      K F htransport p
        (q + momentWeakJointRealTimeShift n h))
    hright
  exact Filter.Eventually.of_forall fun r =>
    momentWeakJointCoverTailUpperEnvelope_time_translate_le
      K F htransport p r hh q
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
