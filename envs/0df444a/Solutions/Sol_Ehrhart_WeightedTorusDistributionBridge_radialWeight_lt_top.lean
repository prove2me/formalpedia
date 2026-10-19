-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.radialWeight_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/9b53662f-54e8-4262-88d1-2f17e8ff70d7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusDistributionBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18903
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18906
namespace Ehrhart.WeightedTorusDistributionBridge
theorem _root_.solution {n k : ℕ}
    (φ : Space n → ℝ) (x : Space n) :
    WeightedTorusHilbert.radialWeight k φ x < ⊤ := by
  unfold WeightedTorusHilbert.radialWeight
  exact ENNReal.ofReal_lt_top
end Ehrhart.WeightedTorusDistributionBridge
