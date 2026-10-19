-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicApproximation.integrable_momentWeakHolomorphicJointRadialEnvelopeCircleAverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/65b4bb69-71b6-404d-b27b-40970bb8ceb8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicApproximation_integrable_momentWeakHolomorphicJointRadialEnvelopeCircleIntegrand

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
    Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y *
          Real.circleAverage
            (fun w : ℂ =>
              momentWeakJointCoverUpperEnvelope K F htransport p
                (q - w • y)) 0 1)
      (volume : Measure (SourceJointComplexCover n)) := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have hinner :
      Integrable
        (fun y : SourceJointComplexCover n =>
          ∫ θ : ℝ,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope K F htransport p
                (q - circleMap 0 1 θ • y) ∂ν)
        (volume : Measure (SourceJointComplexCover n)) :=
    (integrable_momentWeakHolomorphicJointRadialEnvelopeCircleIntegrand
      K F htransport p k q).integral_prod_left
  refine (hinner.const_mul ((2 * Real.pi)⁻¹)).congr ?_
  filter_upwards [] with y
  rw [Real.circleAverage_def]
  change
    (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - circleMap 0 1 θ • y) ∂ν) =
      sourceJointTrueRadialMollifier n k y *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in 0..2 * Real.pi,
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - circleMap 0 1 θ • y)))
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  change
    (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - circleMap 0 1 θ • y) ∂ν) =
      sourceJointTrueRadialMollifier n k y *
        ((2 * Real.pi)⁻¹ *
          (∫ θ : ℝ,
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - circleMap 0 1 θ • y) ∂ν))
  rw [MeasureTheory.integral_const_mul]
  ring
end Ehrhart.BergmanJetJointHolomorphicApproximation
