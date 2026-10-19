-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.contDiff_productRadialKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/c8eed500-3336-4202-818f-5533fd15fc2b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_contDiff_radialCoordinateKernel

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
      (productRadialKernel (n := n)) := by
  unfold productRadialKernel
  apply contDiff_prod
  intro i hi
  apply contDiff_radialCoordinateKernel.comp
  fun_prop
end Ehrhart.WeightedTorusWeylRepresentativeBridge
