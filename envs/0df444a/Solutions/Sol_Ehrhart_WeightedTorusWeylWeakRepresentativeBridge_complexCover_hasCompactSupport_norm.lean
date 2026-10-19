-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexCover_hasCompactSupport_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/875106c2-4611-4b7a-994b-7fb388afda8f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedBrascampSaturation DolbeaultRegularity ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusWeylRepresentativeBridge
open WeightedTorusWeylRadialIntegrationBridge
namespace Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
theorem _root_.solution {n : ℕ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hκ : HasCompactSupport κ) :
    HasCompactSupport (fun z => ‖κ z‖) := by
  refine hκ.mono ?_
  intro z hz
  change ‖κ z‖ ≠ 0 at hz
  change κ z ≠ 0
  intro hzero
  apply hz
  simp [hzero]
end Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
