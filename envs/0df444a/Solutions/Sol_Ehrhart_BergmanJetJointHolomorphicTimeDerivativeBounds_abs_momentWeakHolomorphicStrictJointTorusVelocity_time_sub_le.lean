-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.abs_momentWeakHolomorphicStrictJointTorusVelocity_time_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/d0d28c58-9e21-43b0-b24f-2489dca5ee07

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_jointSourceTorusVelocity_eq_cover
import Theorems.Thm_Ehrhart_RadialAccelerationBounds_sourceJointTrueRadialTimeKernelMass_nonneg
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_abs_jointSourceCoverVelocity_momentWeakHolomorphicJointMollification_time_sub_le
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_momentWeakHolomorphicStrictJointTorusVelocity_eq_mollified

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
    |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q -
      jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) s q| ≤
      BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k * |t - s| := by
  have hc₀ : 0 ≤ 1 - ε := sub_nonneg.mpr hε₁
  have hc₁ : 1 - ε ≤ 1 := sub_le_self 1 hε₀
  have hB : 0 ≤
      BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k * |t - s| :=
    mul_nonneg
      (mul_nonneg (BodyScale.canonicalScale_pos K).le
        (sourceJointTrueRadialTimeKernelMass_nonneg n k))
      (abs_nonneg _)
  rw [momentWeakHolomorphicStrictJointTorusVelocity_eq_mollified
      K F htransport p ε k t q,
    momentWeakHolomorphicStrictJointTorusVelocity_eq_mollified
      K F htransport p ε k s q,
    ← mul_sub, abs_mul, abs_of_nonneg hc₀]
  calc
    (1 - ε) *
        |jointSourceTorusVelocity
            (momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k) t q -
          jointSourceTorusVelocity
            (momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k) s q| ≤
      (1 - ε) *
        (BodyScale.canonicalScale K *
          sourceJointTrueRadialTimeKernelMass n k * |t - s|) := by
        apply mul_le_mul_of_nonneg_left _ hc₀
        rw [jointSourceTorusVelocity_eq_cover,
          jointSourceTorusVelocity_eq_cover]
        exact
          abs_jointSourceCoverVelocity_momentWeakHolomorphicJointMollification_time_sub_le
            K F htransport p (sourceTorusCoverPoint q) k s t
    _ ≤ BodyScale.canonicalScale K *
          sourceJointTrueRadialTimeKernelMass n k * |t - s| := by
      simpa using mul_le_mul_of_nonneg_right hc₁ hB
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
