-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.continuous_realRadialWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/dbf764f1-6a48-4039-bbb6-1aa081cbdc57

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
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Continuous
      (fun z : WeightedTorusHilbert.LogTorus n =>
        Real.exp (-(k : ℝ) * φ z.1)) :=
  Real.continuous_exp.comp
    (continuous_const.mul (hφ.comp continuous_fst))
end Ehrhart.WeightedTorusDistributionBridge
