-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.limsup_momentBodyMovingJetIntegral_ge_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/7382d51f-c947-4cc9-9537-36fbea730765

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_eventually_integral_momentTorusJetSlope_Bergman_ge_sharp
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_integral_momentBodyMovingJetSlope_le_canonicalScale

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
    (p : LogSpace n) :
    (n : ℝ) * BodyScale.canonicalScale K /
        ((n : ℝ) + 1) ≤
      Filter.limsup
        (fun k : ℕ =>
          ∫ q : LogTorus n,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) q
              ∂(momentTorusBergmanProbability
                K (momentBodyOptimizer K) (k + 1))) atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hevent :=
    eventually_integral_momentTorusJetSlope_Bergman_ge_sharp
      hn K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  have hshift :
      ∀ᶠ k : ℕ in atTop,
        (n : ℝ) * BodyScale.canonicalScale K /
            ((n : ℝ) + 1) - ε ≤
          ∫ q : LogTorus n,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) q
              ∂(momentTorusBergmanProbability
                K (momentBodyOptimizer K) (k + 1)) := by
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    exact hN (k + 1) (by omega)
  have hbounded :
      ∀ᶠ k : ℕ in atTop,
        (∫ q : LogTorus n,
          momentTorusJetSlope
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) p (k + 1) q
            ∂(momentTorusBergmanProbability
              K (momentBodyOptimizer K) (k + 1))) ≤
            BodyScale.canonicalScale K :=
    Filter.Eventually.of_forall
      (integral_momentBodyMovingJetSlope_le_canonicalScale K p)
  have hlim := Filter.le_limsup_of_frequently_le hshift.frequently
    (Filter.isBoundedUnder_of_eventually_le hbounded)
  linarith
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
