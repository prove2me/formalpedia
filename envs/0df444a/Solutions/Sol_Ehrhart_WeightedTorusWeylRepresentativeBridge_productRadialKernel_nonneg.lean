-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.productRadialKernel_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/345f054a-ebf0-4b28-9cb6-8866c1dac499

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_radialCoordinateKernel_nonneg

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
theorem _root_.solution {n : ℕ}
    (w : TorusCharacters.LogSpace n) :
    0 ≤ productRadialKernel w := by
  unfold productRadialKernel
  exact Finset.prod_nonneg fun i hi => radialCoordinateKernel_nonneg _
end Ehrhart.WeightedTorusWeylRepresentativeBridge
