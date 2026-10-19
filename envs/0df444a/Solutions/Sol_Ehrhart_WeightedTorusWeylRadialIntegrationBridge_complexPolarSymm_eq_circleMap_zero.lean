-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.complexPolarSymm_eq_circleMap_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/d3cddb1e-4b21-49e4-9793-46d69504e080

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
theorem _root_.solution (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
  simp [Complex.polarCoord_symm_apply, circleMap,
    Complex.exp_mul_I]
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
