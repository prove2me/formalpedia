-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.hasCompactSupport_productRadialWeightedIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/2ea855b6-9422-4b79-b05f-216c3484594d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_hasCompactSupport_productRadialKernel

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
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ) :
    HasCompactSupport (productRadialWeightedIntegrand F) := by
  refine (hasCompactSupport_productRadialKernel n).mono ?_
  intro w hw
  change productRadialKernel w ≠ 0
  intro hzero
  apply hw
  simp [productRadialWeightedIntegrand, hzero]
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
