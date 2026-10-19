-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.compactPolarDomain_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/47e9850b-e7cb-4090-ab00-379ef2d19198

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylRadialIntegrationBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open WeightedTorusWeylRepresentativeBridge
namespace Ehrhart.WeightedTorusWeylRadialIntegrationBridge
theorem _root_.solution :
    (volume : Measure (ℝ × ℝ)).restrict compactPolarDomain =
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioo (-Real.pi) Real.pi)) := by
  unfold compactPolarDomain
  change
    ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi) = _
  exact (MeasureTheory.Measure.prod_restrict
    (Set.Ioc (0 : ℝ) 1) (Set.Ioo (-Real.pi) Real.pi)).symm
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
