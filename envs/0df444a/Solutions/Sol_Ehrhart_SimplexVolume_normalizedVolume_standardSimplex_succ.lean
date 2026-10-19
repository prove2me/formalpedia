-- Prove2me | solution 1 for Ehrhart.SimplexVolume.normalizedVolume_standardSimplex_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/49597562-dd2c-4be0-86db-a75cddecfc46

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_SimplexVolume_normalizedVolume_splitStandardSimplex_fiber_ae
import Theorems.Thm_Ehrhart_SimplexVolume_normalizedVolume_standardSimplex_succ_eq_integral_fibers
import Theorems.Thm_Ehrhart_SimplexVolume_integral_one_sub_pow_Icc

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
    normalizedVolume (standardSimplex (n + 1)) =
      normalizedVolume (standardSimplex n) /
        ((n : ℝ) + 1) := by
  rw [normalizedVolume_standardSimplex_succ_eq_integral_fibers n]
  calc
    (∫ t : ℝ, normalizedVolume
      (Prod.mk t ⁻¹' splitStandardSimplex n)) =
      ∫ t : ℝ, (Set.Icc (0 : ℝ) 1).indicator
        (fun t => (1 - t) ^ n *
          normalizedVolume (standardSimplex n)) t :=
            MeasureTheory.integral_congr_ae
              (normalizedVolume_splitStandardSimplex_fiber_ae n)
    _ = ∫ t in Set.Icc (0 : ℝ) 1,
        (1 - t) ^ n *
          normalizedVolume (standardSimplex n) :=
            MeasureTheory.integral_indicator measurableSet_Icc
    _ = (∫ t in Set.Icc (0 : ℝ) 1, (1 - t) ^ n) *
        normalizedVolume (standardSimplex n) := by
          exact MeasureTheory.integral_mul_const
            (normalizedVolume (standardSimplex n))
            (fun t : ℝ => (1 - t) ^ n)
    _ = normalizedVolume (standardSimplex n) /
        ((n : ℝ) + 1) := by
          rw [integral_one_sub_pow_Icc n]
          ring
end Ehrhart.SimplexVolume
