-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.momentBodyClampedTailPositiveSecant_le_scale_add_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/2ce063a6-96ad-4bbb-8bc2-d66907126d61

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_momentBodyTailPositiveSecant_le_scale_add_inv

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
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) :
    momentBodyClampedTailPositiveSecant K p r t ht q ≤
      BodyScale.canonicalScale K + 1 / t := by
  unfold momentBodyClampedTailPositiveSecant
  apply max_le
  · exact add_nonneg (BodyScale.canonicalScale_pos K).le
      (by positivity)
  · exact momentBodyTailPositiveSecant_le_scale_add_inv
      K p r t ht q
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
