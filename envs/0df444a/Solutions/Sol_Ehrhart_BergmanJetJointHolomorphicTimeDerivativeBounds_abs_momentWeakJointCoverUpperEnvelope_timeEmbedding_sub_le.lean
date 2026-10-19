-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.abs_momentWeakJointCoverUpperEnvelope_timeEmbedding_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/04e3984f-f322-42f4-af87-74b947215b25

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_momentWeakJointCoverUpperEnvelope_le_time_translate
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_momentWeakJointCoverUpperEnvelope_time_translate_le
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_sourceJointTimeEmbedding_sub_eq_add_realTimeShift

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
    (p z : LogSpace n) (y : SourceJointComplexCover n)
    (s t : ℝ) :
    |momentWeakJointCoverUpperEnvelope
        K F htransport p (sourceJointTimeEmbedding z t - y) -
      momentWeakJointCoverUpperEnvelope
        K F htransport p (sourceJointTimeEmbedding z s - y)| ≤
      BodyScale.canonicalScale K * |t - s| := by
  rcases le_total s t with hst | hts
  · have hh : 0 ≤ t - s := sub_nonneg.mpr hst
    have hident :=
      sourceJointTimeEmbedding_sub_eq_add_realTimeShift
        z y s t
    have hmono := momentWeakJointCoverUpperEnvelope_le_time_translate
      K F htransport p hh (sourceJointTimeEmbedding z s - y)
    have hupper :=
      momentWeakJointCoverUpperEnvelope_time_translate_le
        K F htransport p hh (sourceJointTimeEmbedding z s - y)
    rw [hident]
    rw [abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonneg hh]
    linarith
  · have hh : 0 ≤ s - t := sub_nonneg.mpr hts
    have hident :=
      sourceJointTimeEmbedding_sub_eq_add_realTimeShift
        z y t s
    have hmono := momentWeakJointCoverUpperEnvelope_le_time_translate
      K F htransport p hh (sourceJointTimeEmbedding z t - y)
    have hupper :=
      momentWeakJointCoverUpperEnvelope_time_translate_le
        K F htransport p hh (sourceJointTimeEmbedding z t - y)
    rw [hident]
    rw [abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hts)]
    linarith
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
