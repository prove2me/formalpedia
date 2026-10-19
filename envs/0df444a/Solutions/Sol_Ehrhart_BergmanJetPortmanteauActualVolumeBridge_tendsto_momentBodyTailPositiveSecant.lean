-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.tendsto_momentBodyTailPositiveSecant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/f3a7d26b-a44b-481f-956d-ff13f3f867b4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetEnvelopeLimit_tendsto_momentJointTailUpperEnvelope

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
      (fun r : ℕ => momentBodyTailPositiveSecant K p r t ht q)
      atTop
      (𝓝 (momentBodyEnvelopePositiveSecant K p t q)) := by
  have htail :=
    tendsto_momentJointTailUpperEnvelope
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p
          (sourcePositiveJointTimePoint (sourceTorusCoverPoint q) t ht)
  have hsec :=
    (htail.sub (tendsto_const_nhds
      (x := momentNormalizedPotential
        (momentBodyOptimizer K) q.1))).div_const t
  simpa [momentBodyTailPositiveSecant,
    momentTorusTailUpperEnvelopeTimeSlice,
    momentBodyEnvelopePositiveSecant,
    momentBodyTorusWeight,
    momentTorusEnvelopeTimeSlice,
    momentEnvelopeTimeSlice, ht,
    realLogCoordinate_sourceTorusCoverPoint] using hsec
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
