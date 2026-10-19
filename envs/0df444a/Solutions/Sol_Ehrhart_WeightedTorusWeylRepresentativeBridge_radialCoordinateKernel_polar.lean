-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.radialCoordinateKernel_polar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/f3b41c14-0a1d-4e6d-af25-ecd40ceb9206

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
theorem _root_.solution (r θ : ℝ) :
    radialCoordinateKernel
      (Complex.polarCoord.symm (r, θ)) =
      Real.smoothTransition (1 - r ^ 2) := by
  simp [radialCoordinateKernel, Complex.normSq_eq_norm_sq,
    sq_abs]
end Ehrhart.WeightedTorusWeylRepresentativeBridge
