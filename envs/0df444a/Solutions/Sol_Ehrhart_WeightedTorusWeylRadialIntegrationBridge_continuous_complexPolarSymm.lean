-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.continuous_complexPolarSymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/3e3ac4eb-51a7-4f73-8624-6f837c237a2f

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
    Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  simp only [Complex.polarCoord_symm_apply]
  fun_prop
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
