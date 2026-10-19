-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicApproximation.momentWeakHolomorphicJointRadialEnvelopeAngleIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/3cbb205a-5d51-48b2-8d74-db921042a333

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeTrueRadialMollifier_sourceJointTrueRadialMollifier_phase
import Theorems.Thm_Ehrhart_JetEnvelopeTrueRadialMollifier_integral_sourceJointComplexPhase

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
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) (θ : ℝ) :
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        momentWeakJointCoverUpperEnvelope K F htransport p
          (q - circleMap 0 1 θ • y)) =
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope K F htransport p (q - y) := by
  let w : ℂ := circleMap 0 1 θ
  have hw : ‖w‖ = 1 := by
    simp [w, norm_circleMap_zero]
  calc
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        momentWeakJointCoverUpperEnvelope K F htransport p (q - w • y)) =
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k (w • y) *
          momentWeakJointCoverUpperEnvelope K F htransport p
            (q - w • y) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with y
              rw [sourceJointTrueRadialMollifier_phase k w hw y]
    _ = ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope K F htransport p (q - y) :=
      integral_sourceJointComplexPhase w hw
        (fun y : SourceJointComplexCover n =>
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope K F htransport p (q - y))
end Ehrhart.BergmanJetJointHolomorphicApproximation
