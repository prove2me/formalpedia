-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.abs_jointSourceCoverVelocity_momentWeakHolomorphicJointMollification_time_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/920e2481-df24-4036-9b97-301972a8e820

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_RadialAccelerationBounds_hasCompactSupport_sourceJointTrueRadialTimeKernel
import Theorems.Thm_Ehrhart_RadialAccelerationBounds_continuous_sourceJointTrueRadialTimeKernel
import Theorems.Thm_Ehrhart_RadialAccelerationBounds_integrable_sourceJointTrueRadialTimeKernel
import Theorems.Thm_Ehrhart_RadialAccelerationBounds_jointSourceCoverVelocity_sourceJointTrueRadialSmoothed
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
    |jointSourceCoverVelocity
        (momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k)
          (sourceJointTimeEmbedding z t) -
      jointSourceCoverVelocity
        (momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k)
          (sourceJointTimeEmbedding z s)| ≤
      BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k * |t - s| := by
  let ρ : SourceJointComplexCover n → ℝ :=
    sourceJointTrueRadialTimeKernel n k
  let E : SourceJointComplexCover n → ℝ :=
    momentWeakJointCoverUpperEnvelope K F htransport p
  let B : ℝ := BodyScale.canonicalScale K * |t - s|
  have hE : LocallyIntegrable E
      (volume : Measure (SourceJointComplexCover n)) :=
    locallyIntegrable_momentWeakJointCoverUpperEnvelope
      K F htransport p
  have hρ : Integrable ρ
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialTimeKernel n k
  have ht : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z t - y))
      (volume : Measure (SourceJointComplexCover n)) := by
    have hconv :=
      (hasCompactSupport_sourceJointTrueRadialTimeKernel n k).convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (continuous_sourceJointTrueRadialTimeKernel n k)
        hE (sourceJointTimeEmbedding z t)
    refine hconv.integrable.congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp [ρ, E, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hs : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z s - y))
      (volume : Measure (SourceJointComplexCover n)) := by
    have hconv :=
      (hasCompactSupport_sourceJointTrueRadialTimeKernel n k).convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (continuous_sourceJointTrueRadialTimeKernel n k)
        hE (sourceJointTimeEmbedding z s)
    refine hconv.integrable.congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp [ρ, E, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hd : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y))
      (volume : Measure (SourceJointComplexCover n)) := ht.sub hs
  have hmajor : Integrable
      (fun y : SourceJointComplexCover n => |ρ y| * B)
      (volume : Measure (SourceJointComplexCover n)) := by
    simpa [Real.norm_eq_abs] using hρ.norm.mul_const B
  have hpoint (y : SourceJointComplexCover n) :
      ‖ρ y * E (sourceJointTimeEmbedding z t - y) -
        ρ y * E (sourceJointTimeEmbedding z s - y)‖ ≤
          |ρ y| * B := by
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_momentWeakJointCoverUpperEnvelope_timeEmbedding_sub_le
        K F htransport p z y s t)
      (abs_nonneg _)
  rw [show
    jointSourceCoverVelocity
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)
      (sourceJointTimeEmbedding z t) =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (SourceJointComplexCover n))] E)
        (sourceJointTimeEmbedding z t) from
          jointSourceCoverVelocity_sourceJointTrueRadialSmoothed
            hE k (sourceJointTimeEmbedding z t),
    show
    jointSourceCoverVelocity
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)
      (sourceJointTimeEmbedding z s) =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (SourceJointComplexCover n))] E)
        (sourceJointTimeEmbedding z s) from
          jointSourceCoverVelocity_sourceJointTrueRadialSmoothed
            hE k (sourceJointTimeEmbedding z s)]
  rw [MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub ht hs, ← Real.norm_eq_abs]
  calc
    ‖∫ y : SourceJointComplexCover n,
        (ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y))‖ ≤
      ∫ y : SourceJointComplexCover n,
        ‖ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : SourceJointComplexCover n, |ρ y| * B :=
      integral_mono hd.norm hmajor hpoint
    _ = sourceJointTrueRadialTimeKernelMass n k * B := by
      rw [integral_mul_const]
      rfl
    _ = BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k * |t - s| := by
      dsimp [B]
      ring
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
