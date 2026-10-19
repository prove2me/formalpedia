-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.integrable_momentBodyMovingJetSlope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/54d0bead-2568-4208-acc1-706443d755a5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentTorusJetSlope_nonneg
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentTorusJetSlope_le_canonicalScale
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_continuous_momentTorusJetSlope

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
    Integrable
      (momentTorusJetSlope
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p (k + 1))
      (momentTorusBergmanProbability
        K (momentBodyOptimizer K) (k + 1)) := by
  let : IsProbabilityMeasure
      (momentTorusBergmanProbability
        K (momentBodyOptimizer K) (k + 1)) :=
    momentTorusBergmanProbability_isProbability
      K (Nat.zero_lt_succ k) (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K)
  refine
    (integrable_const (BodyScale.canonicalScale K)).mono'
      (continuous_momentTorusJetSlope
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p (k + 1)).aestronglyMeasurable
      ?_
  exact Filter.Eventually.of_forall fun q => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (momentTorusJetSlope_nonneg
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p (k + 1) q)]
    exact momentTorusJetSlope_le_canonicalScale
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p (k + 1) q
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
