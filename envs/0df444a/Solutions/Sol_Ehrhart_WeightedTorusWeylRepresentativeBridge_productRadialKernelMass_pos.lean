-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.productRadialKernelMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/1679488f-d20d-458e-af7f-115b05f6d8a7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_contDiff_productRadialKernel
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_productRadialKernel_nonneg
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_hasCompactSupport_productRadialKernel

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
    0 < productRadialKernelMass n := by
  unfold productRadialKernelMass
  apply (contDiff_productRadialKernel n).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_productRadialKernel n)
    (fun w => productRadialKernel_nonneg w)
    (x := (0 : TorusCharacters.LogSpace n))
  simp [productRadialKernel, radialCoordinateKernel]
end Ehrhart.WeightedTorusWeylRepresentativeBridge
