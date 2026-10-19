-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.abs_momentWeakHolomorphicStrictJointTorusVelocity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/4a3944e5-73ff-4a3a-b1c7-dc6d47ba21ff

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_hasDerivAt_jointSourceTorusWeight
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_abs_momentWeakHolomorphicStrictJointTorusWeight_time_sub_le

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
    |jointSourceTorusVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) t q| ≤
      BodyScale.canonicalScale K := by
  have hG : ContDiff ℝ 2
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) :=
    (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2
  have hderiv := hasDerivAt_jointSourceTorusWeight hG t q
  have hlip :
      ∀ᶠ u : ℝ in 𝓝 t,
        ‖jointSourceTorusWeight
              (momentWeakHolomorphicStrictJointCoverWeight
                K F htransport p ε k) u q -
            jointSourceTorusWeight
              (momentWeakHolomorphicStrictJointCoverWeight
                K F htransport p ε k) t q‖ ≤
          BodyScale.canonicalScale K * ‖u - t‖ := by
    exact Filter.Eventually.of_forall fun u => by
      simpa [Real.norm_eq_abs,
        momentWeakHolomorphicStrictJointTorusWeight] using
          abs_momentWeakHolomorphicStrictJointTorusWeight_time_sub_le
            K F htransport p ε hε₀ hε₁ k t u q
  simpa [Real.norm_eq_abs] using
    hderiv.le_of_lip' (BodyScale.canonicalScale_pos K).le
      hlip
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
