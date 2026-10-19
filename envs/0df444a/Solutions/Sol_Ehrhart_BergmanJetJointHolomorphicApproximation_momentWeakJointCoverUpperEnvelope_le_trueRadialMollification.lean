-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicApproximation.momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/e908bbb0-cc19-4f17-a6fd-419c53b2fc12

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicApproximation_momentWeakHolomorphicJointRadialEnvelopeCircleAverageIntegral
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicApproximation_integrable_momentWeakHolomorphicJointRadialEnvelopeCircleAverage

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
    momentWeakJointCoverUpperEnvelope K F htransport p q ≤
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k q := by
  change momentWeakJointCoverUpperEnvelope K F htransport p q ≤
    sourceJointTrueRadialSmoothed
      (momentWeakJointCoverUpperEnvelope K F htransport p) k q
  unfold sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def]
  change momentWeakJointCoverUpperEnvelope K F htransport p q ≤
    ∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        momentWeakJointCoverUpperEnvelope K F htransport p (q - y)
  rw [← momentWeakHolomorphicJointRadialEnvelopeCircleAverageIntegral
    K F htransport p k q]
  calc
    momentWeakJointCoverUpperEnvelope K F htransport p q =
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope K F htransport p q := by
        rw [MeasureTheory.integral_mul_const,
          integral_sourceJointTrueRadialMollifier, one_mul]
    _ ≤ ∫ y : SourceJointComplexCover n,
          sourceJointTrueRadialMollifier n k y *
            Real.circleAverage
              (fun w : ℂ =>
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - w • y)) 0 1 := by
      apply MeasureTheory.integral_mono
        ((integrable_sourceJointTrueRadialMollifier n k).mul_const
          (momentWeakJointCoverUpperEnvelope K F htransport p q))
        (integrable_momentWeakHolomorphicJointRadialEnvelopeCircleAverage
          K F htransport p k q)
      intro y
      apply mul_le_mul_of_nonneg_left _
        (sourceJointTrueRadialMollifier_nonneg n k y)
      have hmean :=
        momentWeakJointCoverUpperEnvelope_complex_line_submean_all_radius
          K F htransport p q (-y) 1
      simpa [smul_neg, sub_eq_add_neg] using hmean
end Ehrhart.BergmanJetJointHolomorphicApproximation
