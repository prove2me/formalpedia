-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.upperSemicontinuous_momentTorusTailUpperEnvelopeTimeSlice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/fe427e1c-8901-4297-9673-56fbe6f87f8b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualUpperTailBridge_upperSemicontinuous_periodic_real_torusRepresentative
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualUpperTailBridge_continuous_sourcePositiveJointTimePoint_fixed
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualUpperTailBridge_momentJointTailUpperEnvelope_timeSlice_periodic

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge JetEnvelopeRightDerivative EnvelopeSpatialPeriodicity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation BergmanJetUpperEnvelope
open BergmanJetSpatialPeriodicity BergmanJetPortmanteauSlopeBridge
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    UpperSemicontinuous
      (momentTorusTailUpperEnvelopeTimeSlice
        K F htransport p r t ht) := by
  unfold momentTorusTailUpperEnvelopeTimeSlice
  apply upperSemicontinuous_periodic_real_torusRepresentative
    (fun z : LogSpace n =>
      momentJointTailUpperEnvelope K F htransport p r
        (sourcePositiveJointTimePoint z t ht))
    (momentJointTailUpperEnvelope_timeSlice_periodic
      K F htransport p r t ht)
  exact (upperSemicontinuous_momentJointTailUpperEnvelope
    K F htransport p r).comp
      (continuous_sourcePositiveJointTimePoint_fixed t ht)
end Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
