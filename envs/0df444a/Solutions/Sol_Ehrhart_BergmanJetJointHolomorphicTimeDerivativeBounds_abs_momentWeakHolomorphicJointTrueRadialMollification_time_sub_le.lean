-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.abs_momentWeakHolomorphicJointTrueRadialMollification_time_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/c6590f4b-c7df-4e73-808d-355d777e5790

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_abs_momentWeakJointCoverUpperEnvelope_timeEmbedding_sub_le

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
    (p z : LogSpace n) (k : ℕ) (s t : ℝ) :
    |momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k (sourceJointTimeEmbedding z t) -
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k (sourceJointTimeEmbedding z s)| ≤
      BodyScale.canonicalScale K * |t - s| := by
  let ρ : SourceJointComplexCover n → ℝ :=
    sourceJointTrueRadialMollifier n k
  let E : SourceJointComplexCover n → ℝ :=
    momentWeakJointCoverUpperEnvelope K F htransport p
  let B : ℝ := BodyScale.canonicalScale K * |t - s|
  have hρ : Integrable ρ
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialMollifier n k
  have ht : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z t - y))
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialMollifier_mul_translate
      (locallyIntegrable_momentWeakJointCoverUpperEnvelope
        K F htransport p)
      k (sourceJointTimeEmbedding z t)
  have hs : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z s - y))
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialMollifier_mul_translate
      (locallyIntegrable_momentWeakJointCoverUpperEnvelope
        K F htransport p)
      k (sourceJointTimeEmbedding z s)
  have hd : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y))
      (volume : Measure (SourceJointComplexCover n)) := ht.sub hs
  have hB : Integrable
      (fun y : SourceJointComplexCover n => ρ y * B)
      (volume : Measure (SourceJointComplexCover n)) :=
    hρ.mul_const B
  have hpoint (y : SourceJointComplexCover n) :
      ‖ρ y * E (sourceJointTimeEmbedding z t - y) -
        ρ y * E (sourceJointTimeEmbedding z s - y)‖ ≤
          ρ y * B := by
    have hnonneg : 0 ≤ ρ y :=
      sourceJointTrueRadialMollifier_nonneg n k y
    calc
      ‖ρ y * E (sourceJointTimeEmbedding z t - y) -
        ρ y * E (sourceJointTimeEmbedding z s - y)‖ =
        ρ y *
          |E (sourceJointTimeEmbedding z t - y) -
            E (sourceJointTimeEmbedding z s - y)| := by
          rw [← mul_sub, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg hnonneg]
      _ ≤ ρ y * B := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        exact
          abs_momentWeakJointCoverUpperEnvelope_timeEmbedding_sub_le
            K F htransport p z y s t
  change
    |sourceJointTrueRadialSmoothed E k
        (sourceJointTimeEmbedding z t) -
      sourceJointTrueRadialSmoothed E k
        (sourceJointTimeEmbedding z s)| ≤ B
  unfold sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  change
    |(∫ y : SourceJointComplexCover n,
        ρ y * E (sourceJointTimeEmbedding z t - y)) -
      (∫ y : SourceJointComplexCover n,
        ρ y * E (sourceJointTimeEmbedding z s - y))| ≤ B
  rw [← MeasureTheory.integral_sub ht hs, ← Real.norm_eq_abs]
  calc
    ‖∫ y : SourceJointComplexCover n,
        (ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y))‖ ≤
      ∫ y : SourceJointComplexCover n,
        ‖ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ y : SourceJointComplexCover n, ρ y * B :=
      MeasureTheory.integral_mono hd.norm hB hpoint
    _ = B := by
      rw [MeasureTheory.integral_mul_const]
      change
        (∫ y : SourceJointComplexCover n,
          sourceJointTrueRadialMollifier n k y) * B = B
      rw [integral_sourceJointTrueRadialMollifier, one_mul]
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
