-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.integral_momentBodyMovingJetSlope_le_canonicalScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/dd9ea66d-8d12-4b38-b84e-c2ece0643da3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentTorusJetSlope_le_canonicalScale
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_integrable_momentBodyMovingJetSlope

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
    (p : LogSpace n) (k : ℕ) :
    (∫ q : LogTorus n,
      momentTorusJetSlope
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p (k + 1) q
        ∂(momentTorusBergmanProbability
          K (momentBodyOptimizer K) (k + 1))) ≤
      BodyScale.canonicalScale K := by
  let : IsProbabilityMeasure
      (momentTorusBergmanProbability
        K (momentBodyOptimizer K) (k + 1)) :=
    momentTorusBergmanProbability_isProbability
      K (Nat.zero_lt_succ k) (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K)
  have h := integral_mono
    (integrable_momentBodyMovingJetSlope K p k)
    (integrable_const (BodyScale.canonicalScale K))
    (fun q => momentTorusJetSlope_le_canonicalScale
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p (k + 1) q)
  simpa using h
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
