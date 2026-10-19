-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.radialWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/58557be2-78e2-4250-8f2a-e112ad5b4be2

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
    0 < WeightedTorusHilbert.radialWeight k φ x := by
  unfold WeightedTorusHilbert.radialWeight
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
end Ehrhart.WeightedTorusDistributionBridge
