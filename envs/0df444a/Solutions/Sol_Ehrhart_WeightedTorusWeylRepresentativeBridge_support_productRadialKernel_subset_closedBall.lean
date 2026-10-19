-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.support_productRadialKernel_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/6603ee72-f9b7-413b-88d0-aff57c6748e5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_radialCoordinateKernel_eq_zero_iff

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
    Function.support (productRadialKernel (n := n)) ⊆
      Metric.closedBall
        (0 : TorusCharacters.LogSpace n) 1 := by
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  by_contra hi
  have hzero : radialCoordinateKernel (w i) = 0 :=
    (radialCoordinateKernel_eq_zero_iff _).2
      (le_of_lt (lt_of_not_ge hi))
  change (∏ j : Fin n, radialCoordinateKernel (w j)) ≠ 0 at hw
  exact hw (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
end Ehrhart.WeightedTorusWeylRepresentativeBridge
