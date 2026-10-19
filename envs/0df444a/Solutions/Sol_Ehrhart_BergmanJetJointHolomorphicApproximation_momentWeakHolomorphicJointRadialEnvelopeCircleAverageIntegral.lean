-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicApproximation.momentWeakHolomorphicJointRadialEnvelopeCircleAverageIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/04233f98-a783-47d1-99a0-5ca9e639195a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicApproximation_integrable_momentWeakHolomorphicJointRadialEnvelopeCircleIntegrand
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicApproximation_momentWeakHolomorphicJointRadialEnvelopeAngleIntegral

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicApproximation
open Set Function Filter MeasureTheory Metric
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicClosure BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialMollifier
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
attribute [local instance] Ehrhart.BergmanJetJointHolomorphicApproximation.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.BergmanJetJointHolomorphicApproximation
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : SourceJointComplexCover n) :
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - w • y)) 0 1) =
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope K F htransport p (q - y) := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have hswap :
      (∫ y : SourceJointComplexCover n,
        ∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - circleMap 0 1 θ • y) ∂ν) =
        ∫ θ : ℝ,
          (∫ y : SourceJointComplexCover n,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope K F htransport p
                (q - circleMap 0 1 θ • y)) ∂ν := by
    exact MeasureTheory.integral_integral_swap
      (integrable_momentWeakHolomorphicJointRadialEnvelopeCircleIntegrand
        K F htransport p k q)
  calc
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - w • y)) 0 1) =
      ∫ y : SourceJointComplexCover n,
        (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope K F htransport p
                (q - circleMap 0 1 θ • y) ∂ν := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        rw [Real.circleAverage_def]
        change
          sourceJointTrueRadialMollifier n k y *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in 0..2 * Real.pi,
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - circleMap 0 1 θ • y))) =
            (2 * Real.pi)⁻¹ *
              (∫ θ : ℝ,
                sourceJointTrueRadialMollifier n k y *
                  momentWeakJointCoverUpperEnvelope K F htransport p
                    (q - circleMap 0 1 θ • y) ∂ν)
        rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
        change
          sourceJointTrueRadialMollifier n k y *
            ((2 * Real.pi)⁻¹ *
              (∫ θ : ℝ,
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - circleMap 0 1 θ • y) ∂ν)) = _
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = (2 * Real.pi)⁻¹ *
          ∫ y : SourceJointComplexCover n,
            ∫ θ : ℝ,
              sourceJointTrueRadialMollifier n k y *
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - circleMap 0 1 θ • y) ∂ν := by
      rw [MeasureTheory.integral_const_mul]
    _ = (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ,
            (∫ y : SourceJointComplexCover n,
              sourceJointTrueRadialMollifier n k y *
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - circleMap 0 1 θ • y)) ∂ν := by
      rw [hswap]
    _ = (2 * Real.pi)⁻¹ *
          ∫ _θ : ℝ,
            (∫ y : SourceJointComplexCover n,
              sourceJointTrueRadialMollifier n k y *
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - y)) ∂ν := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with θ
      exact momentWeakHolomorphicJointRadialEnvelopeAngleIntegral
        K F htransport p k q θ
    _ = ∫ y : SourceJointComplexCover n,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - y) := by
      rw [MeasureTheory.integral_const]
      simp [ν, MeasureTheory.measureReal_def, Real.volume_Ioc,
        Real.pi_pos.le]
      field_simp [Real.pi_ne_zero]
end Ehrhart.BergmanJetJointHolomorphicApproximation
