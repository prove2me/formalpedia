-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.abs_momentWeakHolomorphicStrictJointTorusWeight_time_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/e3dcade0-19a3-4c20-9cc4-c20b92d80141

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_abs_momentWeakHolomorphicJointTrueRadialMollification_time_sub_le

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
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (s t : ℝ) (q : LogTorus n) :
    |momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t q -
      momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k s q| ≤
      BodyScale.canonicalScale K * |t - s| := by
  have hc₀ : 0 ≤ 1 - ε := sub_nonneg.mpr hε₁
  have hc₁ : 1 - ε ≤ 1 := sub_le_self 1 hε₀
  have hB : 0 ≤ BodyScale.canonicalScale K * |t - s| :=
    mul_nonneg (BodyScale.canonicalScale_pos K).le
      (abs_nonneg _)
  rw [momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover,
    momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover]
  unfold momentWeakHolomorphicStrictJointCoverWeight
  simp only [sourceJointTimeEmbedding]
  calc
    |((1 - ε) *
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k
              (sourceTorusCoverPoint q, (t / 2 : ℂ)) +
          ε * matrixSourceCoverPotential
            (momentBodyStrictRadialPotential K)
              (sourceTorusCoverPoint q)) -
        ((1 - ε) *
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k
              (sourceTorusCoverPoint q, (s / 2 : ℂ)) +
          ε * matrixSourceCoverPotential
            (momentBodyStrictRadialPotential K)
              (sourceTorusCoverPoint q))| =
      (1 - ε) *
        |momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k
              (sourceJointTimeEmbedding
                (sourceTorusCoverPoint q) t) -
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k
              (sourceJointTimeEmbedding
                (sourceTorusCoverPoint q) s)| := by
      simp only [sourceJointTimeEmbedding]
      calc
        _ = |(1 - ε) *
          (momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k
              (sourceTorusCoverPoint q, (t / 2 : ℂ)) -
            momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k
                (sourceTorusCoverPoint q, (s / 2 : ℂ)))| := by
          congr 1
          ring
        _ = _ := by
          rw [abs_mul, abs_of_nonneg hc₀]
    _ ≤ (1 - ε) *
          (BodyScale.canonicalScale K * |t - s|) :=
      mul_le_mul_of_nonneg_left
        (abs_momentWeakHolomorphicJointTrueRadialMollification_time_sub_le
          K F htransport p (sourceTorusCoverPoint q) k s t)
        hc₀
    _ ≤ BodyScale.canonicalScale K * |t - s| := by
      simpa using mul_le_mul_of_nonneg_right hc₁ hB
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
