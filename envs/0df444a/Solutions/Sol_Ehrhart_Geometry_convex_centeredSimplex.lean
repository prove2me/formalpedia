-- Prove2me | solution 1 for Ehrhart.Geometry.convex_centeredSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/542e62cc-746c-4319-8d7d-381b6af24a4b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_mem_centeredSimplex_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.Geometry
open Set MeasureTheory
open scoped BigOperators
namespace Ehrhart.Geometry
theorem _root_.solution (n : ℕ) :
    Convex ℝ (centeredSimplex n) := by
  intro x hx y hy a b ha hb hab
  have hx' := mem_centeredSimplex_iff.mp hx
  have hy' := mem_centeredSimplex_iff.mp hy
  apply mem_centeredSimplex_iff.mpr
  constructor
  · intro i
    change -(1 : ℝ) ≤ a * x i + b * y i
    have hax : 0 ≤ a * (x i + 1) := mul_nonneg ha (by linarith [hx'.1 i])
    have hby : 0 ≤ b * (y i + 1) := mul_nonneg hb (by linarith [hy'.1 i])
    nlinarith
  · change (∑ i, (a * x i + b * y i)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * (∑ i, x i) + b * (∑ i, y i)
          ≤ a * 1 + b * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hx'.2 ha)
              (mul_le_mul_of_nonneg_left hy'.2 hb)
      _ = 1 := by simpa using hab
end Ehrhart.Geometry
