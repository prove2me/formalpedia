-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.tendsto_momentBodyClampedTailPositiveSecant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/9fe86831-e093-4efc-92d7-0403daac6a16

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_tendsto_momentBodyTailPositiveSecant

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
    (p : LogSpace n) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) :
    Tendsto
      (fun r : ℕ =>
        momentBodyClampedTailPositiveSecant K p r t ht q)
      atTop
      (𝓝 (max 0 (momentBodyEnvelopePositiveSecant K p t q))) := by
  simpa [momentBodyClampedTailPositiveSecant] using
    (tendsto_const_nhds (x := (0 : ℝ))).max
      (tendsto_momentBodyTailPositiveSecant K p t ht q)
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
