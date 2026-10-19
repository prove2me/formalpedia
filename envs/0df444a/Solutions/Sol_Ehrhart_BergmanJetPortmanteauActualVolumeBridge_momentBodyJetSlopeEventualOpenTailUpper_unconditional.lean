-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.momentBodyJetSlopeEventualOpenTailUpper_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/460217ee-3a36-4ac5-af16-bdbfbb6fae50

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeJointNeighborhoodUpper_eventual_open_momentTorusJetSlope_lt_clampedTailSecant

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
    ∀ (q : LogTorus n) (a : ℝ),
      momentBodyClampedTailPositiveSecant K p r t ht q < a →
        ∃ (N : ℕ) (U : Set (LogTorus n)), IsOpen U ∧ q ∈ U ∧
          ∀ k : ℕ, N ≤ k → ∀ y ∈ U,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) y < a := by
  intro q a ha
  have ha' :
      momentTorusClampedTailPositiveSecant
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p r t ht q < a := by
    simpa [momentTorusClampedTailPositiveSecant,
      momentTorusTailPositiveSecant,
      momentBodyClampedTailPositiveSecant,
      momentBodyTailPositiveSecant] using ha
  obtain ⟨N, U, hU, hq, hfinite⟩ :=
    eventual_open_momentTorusJetSlope_lt_clampedTailSecant
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K)
        p r t ht q a ha'
  refine ⟨N, U, hU, hq, ?_⟩
  intro k hk y hy
  exact hfinite (k + 1) (by omega) y hy
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
