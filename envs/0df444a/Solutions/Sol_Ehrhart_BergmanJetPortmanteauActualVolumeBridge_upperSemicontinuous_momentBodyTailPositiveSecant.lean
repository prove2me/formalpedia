-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.upperSemicontinuous_momentBodyTailPositiveSecant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/9aa370f3-f5af-4540-b4e1-aea5e72bc6fb

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeJointNeighborhoodUpper_upperSemicontinuous_momentTorusTailPositiveSecant

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
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    UpperSemicontinuous
      (momentBodyTailPositiveSecant K p r t ht) := by
  have h := upperSemicontinuous_momentTorusTailPositiveSecant
    K (momentBodyOptimizer K)
      (momentBodyOptimizer_transport K) p r t ht
  have hsecant :
      momentTorusTailPositiveSecant
          K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p r t ht =
        momentBodyTailPositiveSecant K p r t ht := by
    funext q
    rfl
  rw [hsecant] at h
  exact h
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
