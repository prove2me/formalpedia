-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexCover_real_convolution_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/21d573eb-1cee-46cf-a0df-a04a125106e9

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
    (κ η : TorusCharacters.LogSpace n → ℝ) :
    (κ ⋆[ContinuousLinearMap.mul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] η) =
      (η ⋆[ContinuousLinearMap.mul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))] κ) := by
  have h := MeasureTheory.convolution_flip
    (μ := (volume : Measure (TorusCharacters.LogSpace n)))
    (f := η) (g := κ) (ContinuousLinearMap.mul ℝ ℝ)
  rw [ContinuousLinearMap.flip_mul] at h
  exact h
end Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
