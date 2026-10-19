-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.radialCoordinateKernel_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/0e351397-5c9d-451d-9a2e-abd92931ad1c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution (w : ℂ) :
    radialCoordinateKernel w = 0 ↔ 1 ≤ ‖w‖ := by
  simp [radialCoordinateKernel, Complex.one_le_normSq_iff]
end Ehrhart.WeightedTorusWeylRepresentativeBridge
