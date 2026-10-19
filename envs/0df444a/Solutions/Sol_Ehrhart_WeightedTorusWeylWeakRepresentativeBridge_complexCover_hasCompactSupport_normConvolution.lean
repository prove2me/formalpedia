-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexCover_hasCompactSupport_normConvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/f784d9d7-7b40-4813-945e-c8314e1d782b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_complexCover_hasCompactSupport_norm

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
    {κ η : TorusCharacters.LogSpace n → ℝ}
    (hκ : HasCompactSupport κ) (hη : HasCompactSupport η) :
    HasCompactSupport
      ((fun z => ‖κ z‖)
        ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))]
            (fun z => ‖η z‖)) := by
  exact (complexCover_hasCompactSupport_norm hκ).convolution
    (ContinuousLinearMap.mul ℝ ℝ)
    (complexCover_hasCompactSupport_norm hη)
end Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
