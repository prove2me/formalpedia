-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.complexPolar_center_sub_eq_circleMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/fe092ed4-4545-45b3-b1fb-aa7e062507fa

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_complexPolarSymm_eq_circleMap_zero

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
theorem _root_.solution
    (c : ℂ) (r θ : ℝ) :
    c - Complex.polarCoord.symm (r, θ) =
      circleMap c (-r) θ := by
  rw [complexPolarSymm_eq_circleMap_zero]
  simp [circleMap]
  ring
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
