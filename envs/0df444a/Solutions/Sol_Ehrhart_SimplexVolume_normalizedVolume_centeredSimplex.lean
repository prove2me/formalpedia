-- Prove2me | solution 1 for Ehrhart.SimplexVolume.normalizedVolume_centeredSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/9c7bd480-0747-42d2-9009-68ee84483d2d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_SimplexVolume_normalizedVolume_standardSimplex
import Theorems.Thm_Ehrhart_SimplexVolume_normalizedVolume_centeredSimplex_eq_scale_mul

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
theorem _root_.solution (n : ℕ) (_hn : 0 < n) :
    normalizedVolume (centeredSimplex n) =
      sharpConstant n := by
  rw [normalizedVolume_centeredSimplex_eq_scale_mul n,
    normalizedVolume_standardSimplex n]
  simp [sharpConstant, div_eq_mul_inv]
end Ehrhart.SimplexVolume
