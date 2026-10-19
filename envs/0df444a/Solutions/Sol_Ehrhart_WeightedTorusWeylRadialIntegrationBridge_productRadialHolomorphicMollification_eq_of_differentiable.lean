-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.productRadialHolomorphicMollification_eq_of_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/b8ae827d-f090-46f6-acd1-e5aecd535fbb

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_normalizedProductRadial_holomorphic_integral

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
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F) :
    productRadialHolomorphicMollification F = F := by
  funext z
  unfold productRadialHolomorphicMollification
  rw [MeasureTheory.convolution_def]
  change
    (∫ w : TorusCharacters.LogSpace n,
      normalizedProductRadialKernel w • F (z - w)) = F z
  exact normalizedProductRadial_holomorphic_integral hF z
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
