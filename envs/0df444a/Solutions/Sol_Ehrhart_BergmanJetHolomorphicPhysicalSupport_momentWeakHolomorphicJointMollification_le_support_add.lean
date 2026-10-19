-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalSupport.momentWeakHolomorphicJointMollification_le_support_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/4ffbc979-882a-4747-9558-9adda3ffd95e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentWeakBergman_momentNormalizedPotential_le_support_add
import Theorems.Thm_Ehrhart_BergmanJetSpatialSmoothing_supportFunction_realLogCoordinate_sub_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetHolomorphicPhysicalSupport
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert BergmanDiagonalBasisIndependence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative JetEnvelopeTrueRadialMollifier
open EnvelopeSmoothing EnvelopeGeneralTorusDescent RadialPartitionBounds MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentWeakBergman BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetSpatialSmoothing
open BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicStrictSchur
open BergmanJetHolomorphicPhysicalMeasure WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology ContDiff Convolution
namespace Ehrhart.BergmanJetHolomorphicPhysicalSupport
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k q ≤
      SupportFunction.supportFunction K.carrier
        (realLogCoordinate q.1) +
      momentWeakHolomorphicJointMollifierSupportError K F q := by
  let C : ℝ :=
    SupportFunction.supportFunction K.carrier
        (realLogCoordinate q.1) +
      momentWeakHolomorphicJointMollifierSupportError K F q
  have hleft : Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope
            K F htransport p (q - y))
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialMollifier_mul_translate
      (locallyIntegrable_momentWeakJointCoverUpperEnvelope
        K F htransport p) k q
  have hright : Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y * C)
      (volume : Measure (SourceJointComplexCover n)) :=
    (integrable_sourceJointTrueRadialMollifier n k).mul_const C
  change _ ≤ C
  unfold momentWeakHolomorphicJointTrueRadialMollification
    sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def]
  calc
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        momentWeakJointCoverUpperEnvelope
          K F htransport p (q - y)) ≤
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y * C := by
      apply MeasureTheory.integral_mono hleft hright
      intro y
      by_cases hy : sourceJointTrueRadialMollifier n k y = 0
      · simp [hy]
      · apply mul_le_mul_of_nonneg_left _
          (sourceJointTrueRadialMollifier_nonneg n k y)
        have hball :=
          support_sourceJointTrueRadialMollifier_subset_closedBall k hy
        have hynorm : ‖y‖ ≤ (1 : ℝ) := by
          have hsmall :
              ‖y‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hball
          have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.zero_lt_succ k
          have hradius : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
            apply (div_le_iff₀ hk).mpr
            norm_num
          exact hsmall.trans hradius
        have hyfst : ‖y.1‖ ≤ (1 : ℝ) :=
          (norm_fst_le y).trans hynorm
        have hnR :
            0 ≤ (n : ℝ) *
              LaurentJetSeparatedness.bodyRadius K :=
          mul_nonneg (Nat.cast_nonneg n)
            (LaurentJetSeparatedness.bodyRadius_pos K).le
        have hsupport :
            SupportFunction.supportFunction K.carrier
              (realLogCoordinate (q - y).1) ≤
            SupportFunction.supportFunction K.carrier
              (realLogCoordinate q.1) +
              ((n : ℝ) *
                LaurentJetSeparatedness.bodyRadius K) * 2 := by
          calc
            SupportFunction.supportFunction K.carrier
                (realLogCoordinate (q - y).1) =
              SupportFunction.supportFunction K.carrier
                (realLogCoordinate (q.1 - y.1)) := rfl
            _ ≤ SupportFunction.supportFunction K.carrier
                  (realLogCoordinate q.1) +
                ((n : ℝ) *
                    LaurentJetSeparatedness.bodyRadius K) *
                  (2 * ‖y.1‖) :=
              supportFunction_realLogCoordinate_sub_le K
                (LaurentJetSeparatedness.bodyRadius_pos K).le
                (fun u hu =>
                  LaurentJetSeparatedness.norm_le_bodyRadius
                    K u hu)
                q.1 y.1
            _ ≤ SupportFunction.supportFunction K.carrier
                  (realLogCoordinate q.1) +
                ((n : ℝ) *
                    LaurentJetSeparatedness.bodyRadius K) *
                  2 := by
              have htwo : (2 : ℝ) * ‖y.1‖ ≤ 2 := by
                linarith
              exact add_le_add (le_refl _)
                (mul_le_mul_of_nonneg_left htwo hnR)
        have htime :
            |sourceJointCoverTime (q - y)| ≤
              |sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖ := by
          calc
            |sourceJointCoverTime (q - y)| ≤
                |sourceJointCoverTime q| +
                  ‖sourceJointRealTimeCLM n‖ * ‖y‖ :=
              abs_sourceJointCoverTime_sub_le q y
            _ ≤ |sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖ := by
              exact add_le_add (le_refl _)
                (mul_le_of_le_one_right
                  (norm_nonneg (sourceJointRealTimeCLM n)) hynorm)
        have hmax :
            max (sourceJointCoverTime (q - y)) 0 ≤
              |sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖ := by
          apply max_le
          · exact (le_abs_self _).trans htime
          · exact add_nonneg (abs_nonneg _) (norm_nonneg _)
        have hnormpot :=
          momentNormalizedPotential_le_support_add
            F (realLogCoordinate (q - y).1)
        have hscale := BodyScale.canonicalScale_pos K
        have hscaled := mul_le_mul_of_nonneg_left hmax hscale.le
        change
          SupportFunction.supportFunction K.carrier
              (realLogCoordinate (q.1 - y.1)) ≤
            SupportFunction.supportFunction K.carrier
              (realLogCoordinate q.1) +
              ((n : ℝ) *
                LaurentJetSeparatedness.bodyRadius K) * 2
          at hsupport
        change
          MomentRegularity.momentNormalizedPotential
              F (realLogCoordinate (q.1 - y.1)) ≤
            SupportFunction.supportFunction K.carrier
              (realLogCoordinate (q.1 - y.1)) +
              Real.log
                (finiteEnergySourcePartition F /
                  normalizedVolume K.carrier)
          at hnormpot
        calc
          momentWeakJointCoverUpperEnvelope
              K F htransport p (q - y) ≤
            momentWeakJointCoverFiniteMajorant K F (q - y) :=
              momentWeakJointCoverUpperEnvelope_le_majorant
                K F htransport p (q - y)
          _ ≤ C := by
            dsimp [C,
              momentWeakHolomorphicJointMollifierSupportError,
              momentWeakJointCoverFiniteMajorant]
            linarith
    _ = C := by
      rw [MeasureTheory.integral_mul_const,
        integral_sourceJointTrueRadialMollifier, one_mul]
end Ehrhart.BergmanJetHolomorphicPhysicalSupport
