-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.normalizedVolume_le_sharpConstant_of_momentBodyWeakProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/ec147a48-3f93-47e1-baf7-61278b320fca

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BodyScale_canonicalScale_pow
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_momentBodySharpJetScale_le_dimension_of_weakProbability

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
    (hweak : Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K (0 : LogSpace n)))) :
    normalizedVolume K.carrier ≤ sharpConstant n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbound : BodyScale.canonicalScale K ≤ (n : ℝ) + 1 := by
    nlinarith [(div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp
      (momentBodySharpJetScale_le_dimension_of_weakProbability hn K hweak)]
  change normalizedVolume K.carrier ≤
    ((n : ℝ) + 1) ^ n / (n.factorial : ℝ)
  apply (le_div_iff₀ (by positivity : 0 < (n.factorial : ℝ))).mpr
  simpa [BodyScale.canonicalScale_pow hn K, mul_comm] using
    pow_le_pow_left₀ (BodyScale.canonicalScale_pos K).le hbound n
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
