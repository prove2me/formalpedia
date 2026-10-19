-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.contDiff_normalizedProductRadialKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/7b4055da-919e-4e49-b6f8-564018db41c6

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
open Ehrhart.WeightedTorusWeylRepresentativeBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open DolbeaultRegularity DolbeaultGraphDistributionBridge
namespace Ehrhart.WeightedTorusWeylRepresentativeBridge
theorem _root_.solution (n : ℕ) :
    ContDiff ℝ ∞
      (normalizedProductRadialKernel (n := n)) := by
  unfold normalizedProductRadialKernel
  exact (contDiff_productRadialKernel n).div_const _
end Ehrhart.WeightedTorusWeylRepresentativeBridge
