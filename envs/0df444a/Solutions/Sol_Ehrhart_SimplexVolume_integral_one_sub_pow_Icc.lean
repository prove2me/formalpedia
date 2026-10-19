-- Prove2me | solution 1 for Ehrhart.SimplexVolume.integral_one_sub_pow_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/8d22ea2b-d700-4776-a088-bc7c3711be53

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.SimplexVolume
open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise
namespace Ehrhart.SimplexVolume
theorem _root_.solution (n : ℕ) :
    (∫ t in Set.Icc (0 : ℝ) 1, (1 - t) ^ n) =
      1 / ((n : ℝ) + 1) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) 1,
    integral_pow]
  norm_num
end Ehrhart.SimplexVolume
