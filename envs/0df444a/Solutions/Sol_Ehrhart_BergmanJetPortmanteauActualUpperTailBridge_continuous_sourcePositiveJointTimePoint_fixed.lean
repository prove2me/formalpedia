-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.continuous_sourcePositiveJointTimePoint_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/22a72942-af3b-48eb-a82e-f2c75de8e1ff

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    {n : ℕ} (t : ℝ) (ht : 0 < t) :
    Continuous
      (fun z : LogSpace n => sourcePositiveJointTimePoint z t ht) := by
  unfold sourcePositiveJointTimePoint
  apply Continuous.subtype_mk
  exact continuous_id.prodMk continuous_const
end Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
