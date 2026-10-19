-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.limsup_momentBodyMovingJetIntegral_le_clampedTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/0a7da1e2-94c4-4998-84c9-6f5c79409bbe

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentTorusJetSlope_nonneg
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentTorusJetSlope_le_canonicalScale
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_continuous_momentTorusJetSlope
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_limsup_integral_moving_le_of_probability_tendsto_and_eventual_open_upper
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_upperSemicontinuous_momentBodyClampedTailPositiveSecant
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_momentBodyClampedTailPositiveSecant_nonneg
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_momentBodyClampedTailPositiveSecant_le_scale_add_inv

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
      (𝓝 (momentBodyZeroGibbsProbability K p)))
    (hupper : ∀ (q : LogTorus n) (a : ℝ),
      momentBodyClampedTailPositiveSecant K p r t ht q < a →
        ∃ (N : ℕ) (U : Set (LogTorus n)), IsOpen U ∧ q ∈ U ∧
          ∀ k : ℕ, N ≤ k → ∀ y ∈ U,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) y < a) :
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
          ∂(sourceProbability (momentBodyTorusWeight K p) 0) := by
  let C : ℝ := BodyScale.canonicalScale K + 1 / t
  have hC : 0 ≤ C := add_nonneg
    (BodyScale.canonicalScale_pos K).le (by positivity)
  have hscale : BodyScale.canonicalScale K ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ (1 / t : ℝ) by positivity]
  exact limsup_integral_moving_le_of_probability_tendsto_and_eventual_open_upper
    (momentBodyZeroGibbsProbability K p)
    (momentBodyMovingBergmanProbability K)
    hweak
    (fun k : ℕ =>
      momentTorusJetSlope K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p (k + 1))
    (momentBodyClampedTailPositiveSecant K p r t ht)
    C
    (fun k =>
      (continuous_momentTorusJetSlope
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p (k + 1)).measurable)
    (upperSemicontinuous_momentBodyClampedTailPositiveSecant
      K p r t ht)
    hC
    (fun k q => momentTorusJetSlope_nonneg
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p (k + 1) q)
    (fun k q => (momentTorusJetSlope_le_canonicalScale
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p (k + 1) q).trans
          hscale)
    (momentBodyClampedTailPositiveSecant_nonneg K p r t ht)
    (momentBodyClampedTailPositiveSecant_le_scale_add_inv
      K p r t ht)
    hupper
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
