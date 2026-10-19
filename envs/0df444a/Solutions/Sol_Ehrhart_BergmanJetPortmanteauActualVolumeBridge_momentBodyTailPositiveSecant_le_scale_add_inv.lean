-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.momentBodyTailPositiveSecant_le_scale_add_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/f7c74302-db4c-466c-b49b-7c1b90fbf954

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetUpperEnvelope_momentJointTailUpperEnvelope_le_majorant_add_one

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
    momentBodyTailPositiveSecant K p r t ht q ≤
      BodyScale.canonicalScale K + 1 / t := by
  have hmajor := momentJointTailUpperEnvelope_le_majorant_add_one
    K (momentBodyOptimizer K)
      (momentBodyOptimizer_transport K) p r
        (sourcePositiveJointTimePoint (sourceTorusCoverPoint q) t ht)
  have hmajor' :
      momentTorusTailUpperEnvelopeTimeSlice
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p r t ht q ≤
        momentNormalizedPotential
            (momentBodyOptimizer K) q.1 +
          BodyScale.canonicalScale K * t + 1 := by
    simpa [momentTorusTailUpperEnvelopeTimeSlice,
      momentJointMajorant,
      jointRealCoordinate_sourcePositiveJointTimePoint,
      jointLogTime_sourcePositiveJointTimePoint,
      realLogCoordinate_sourceTorusCoverPoint] using hmajor
  unfold momentBodyTailPositiveSecant
  calc
    (momentTorusTailUpperEnvelopeTimeSlice
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p r t ht q -
        momentNormalizedPotential
          (momentBodyOptimizer K) q.1) / t ≤
      (BodyScale.canonicalScale K * t + 1) / t :=
        (div_le_div_iff_of_pos_right ht).mpr (by linarith)
    _ = BodyScale.canonicalScale K + 1 / t := by
      field_simp
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
