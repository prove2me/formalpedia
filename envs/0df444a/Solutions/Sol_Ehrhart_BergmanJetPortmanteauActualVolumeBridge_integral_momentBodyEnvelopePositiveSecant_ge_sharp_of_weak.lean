-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.integral_momentBodyEnvelopePositiveSecant_ge_sharp_of_weak
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/098d54cb-15c2-4f3d-9e40-fa6caddec744

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_limsup_momentBodyMovingJetIntegral_le_clampedTail_of_weak
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_tendsto_integral_momentBodyClampedTailPositiveSecant
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_limsup_momentBodyMovingJetIntegral_ge_sharp

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauActualVolumeBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative LogPartitionConvexity
open MomentRegularity BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge BergmanJetTorusRightSlopeBridge
open BergmanJetTorusRightSlopeGibbsBridge BergmanJetBodyExponentialSecantBridge
open BergmanJetPortmanteauMovingUpperTailBridge BergmanJetPortmanteauActualUpperTailBridge
open BergmanJetTorusSlopeJointNeighborhoodUpper
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauActualVolumeBridge
theorem _root_.solution
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (p : LogSpace n)
    (hweak : Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)))
    {t : ℝ} (ht : 0 < t) :
    (n : ℝ) * BodyScale.canonicalScale K /
        ((n : ℝ) + 1) ≤
      ∫ q : LogTorus n,
        momentBodyEnvelopePositiveSecant K p t q
          ∂(sourceProbability (momentBodyTorusWeight K p) 0) := by
  apply ge_of_tendsto
    (tendsto_integral_momentBodyClampedTailPositiveSecant
      K p t ht)
  exact Filter.Eventually.of_forall fun r =>
    (limsup_momentBodyMovingJetIntegral_ge_sharp hn K p).trans
      (limsup_momentBodyMovingJetIntegral_le_clampedTail_of_weak
        K p r t ht hweak)
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
