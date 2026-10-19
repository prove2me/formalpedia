-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.upperSemicontinuous_momentBodyClampedTailPositiveSecant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/33325867-9837-4956-b582-14b9b8c27aff

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_upperSemicontinuous_momentBodyTailPositiveSecant

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
      (momentBodyClampedTailPositiveSecant K p r t ht) := by
  unfold momentBodyClampedTailPositiveSecant
  exact (continuous_const.upperSemicontinuous).sup
    (upperSemicontinuous_momentBodyTailPositiveSecant
      K p r t ht)
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
