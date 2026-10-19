-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialCoordinateKernel_holomorphic_integral_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/0eaa2aba-9c3f-49de-a2d3-9e1fd22d3997

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_radialCoordinateKernel_holomorphic_integral

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
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    (∫ w : ℂ, radialCoordinateKernel w • f w) =
      (∫ w : ℂ, radialCoordinateKernel w) • f 0 := by
  have hneg : Differentiable ℂ (fun w : ℂ => f (-w)) := by
    apply hf.comp
    fun_prop
  simpa only [zero_sub, neg_neg, neg_zero] using
    radialCoordinateKernel_holomorphic_integral hneg 0
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
