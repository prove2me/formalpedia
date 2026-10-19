-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.abs_momentWeakHolomorphicStrictJointTorusAcceleration_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/7a140e42-8181-4db0-a483-7b23ec20238f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_hasDerivAt_jointSourceTorusVelocity
import Theorems.Thm_Ehrhart_RadialAccelerationBounds_sourceJointTrueRadialTimeKernelMass_nonneg
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_abs_momentWeakHolomorphicStrictJointTorusVelocity_time_sub_le

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
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    |jointSourceTorusAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤
      BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k := by
  let G : SourceJointComplexCover n → ℝ :=
    momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k
  have hG : ContDiff ℝ 2 G := by
    dsimp [G]
    exact (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2
  have hB : 0 ≤
      BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k :=
    mul_nonneg (BodyScale.canonicalScale_pos K).le
      (sourceJointTrueRadialTimeKernelMass_nonneg n k)
  have hderiv := hasDerivAt_jointSourceTorusVelocity hG t q
  have hlip :
      ∀ᶠ u : ℝ in 𝓝 t,
        ‖jointSourceTorusVelocity G u q -
            jointSourceTorusVelocity G t q‖ ≤
          (BodyScale.canonicalScale K *
            sourceJointTrueRadialTimeKernelMass n k) * ‖u - t‖ := by
    exact Filter.Eventually.of_forall fun u => by
      simpa [G, Real.norm_eq_abs] using
        abs_momentWeakHolomorphicStrictJointTorusVelocity_time_sub_le
          K F htransport p ε hε₀ hε₁ k t u q
  simpa [G, Real.norm_eq_abs] using
    hderiv.le_of_lip' hB hlip
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
