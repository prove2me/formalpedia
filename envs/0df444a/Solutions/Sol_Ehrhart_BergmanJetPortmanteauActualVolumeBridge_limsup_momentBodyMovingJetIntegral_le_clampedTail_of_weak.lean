-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.limsup_momentBodyMovingJetIntegral_le_clampedTail_of_weak
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/5c903bd2-4d90-4d48-974e-deea6a95b7f6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_limsup_momentBodyMovingJetIntegral_le_clampedTail
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_momentBodyJetSlopeEventualOpenTailUpper_unconditional

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
    (hweak : Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p))) :
    Filter.limsup
        (fun k : ℕ =>
          ∫ q : LogTorus n,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) q
              ∂(momentTorusBergmanProbability
                K (momentBodyOptimizer K) (k + 1))) atTop ≤
      ∫ q : LogTorus n,
        momentBodyClampedTailPositiveSecant K p r t ht q
          ∂(sourceProbability (momentBodyTorusWeight K p) 0) :=
  limsup_momentBodyMovingJetIntegral_le_clampedTail
    K p r t ht hweak
      (momentBodyJetSlopeEventualOpenTailUpper_unconditional
        K p r t ht)
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
