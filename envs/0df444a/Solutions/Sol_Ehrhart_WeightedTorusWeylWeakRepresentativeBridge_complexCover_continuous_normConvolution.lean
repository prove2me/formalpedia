-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexCover_continuous_normConvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/25cf1e83-9182-4ab1-9df0-41ae17766faf

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
    (hκcont : Continuous κ) (hκcompact : HasCompactSupport κ)
    (hηcont : Continuous η) (hηcompact : HasCompactSupport η) :
    Continuous
      ((fun z => ‖κ z‖)
        ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))]
            (fun z => ‖η z‖)) := by
  have hκint : Integrable κ
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    hκcont.integrable_of_hasCompactSupport hκcompact
  exact (complexCover_hasCompactSupport_norm hηcompact).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ)
    hκint.norm.locallyIntegrable hηcont.norm
end Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
