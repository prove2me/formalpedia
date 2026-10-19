-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.continuous_productRadialWeightedIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/a393b8e8-c7f4-45d8-9860-d71d60320d91

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_contDiff_productRadialKernel

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
theorem _root_.solution {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Continuous F) :
    Continuous (productRadialWeightedIntegrand F) := by
  unfold productRadialWeightedIntegrand
  exact (Complex.continuous_ofReal.comp
    (contDiff_productRadialKernel n).continuous).mul hF
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
