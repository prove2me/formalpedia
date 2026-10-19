-- Prove2me | solution 1 for Ehrhart.Geometry.mem_interior_centeredSimplex_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/fe88205c-72cb-4a29-83c2-aafdbd133f93

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_mem_centeredSimplex_iff
import Theorems.Thm_Ehrhart_Geometry_isOpen_strict_centered_halfspaces
import Theorems.Thm_Ehrhart_Geometry_coordinate_lt_of_mem_interior_centeredSimplex
import Theorems.Thm_Ehrhart_Geometry_coordinateSum_lt_of_mem_interior_centeredSimplex

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
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    {x : Space n} :
    x ∈ interior (centeredSimplex n) ↔
      (∀ i, -(1 : ℝ) < x i) ∧ (∑ i, x i) < 1 := by
  constructor
  · intro hx
    exact ⟨coordinate_lt_of_mem_interior_centeredSimplex hx,
      coordinateSum_lt_of_mem_interior_centeredSimplex hn hx⟩
  · intro hx
    have hsub :
        {y : Space n |
          (∀ i, -(1 : ℝ) < y i) ∧ (∑ i, y i) < 1} ⊆
          centeredSimplex n := by
      intro y hy
      exact mem_centeredSimplex_iff.mpr
        ⟨fun i => (hy.1 i).le, hy.2.le⟩
    exact (interior_maximal hsub (isOpen_strict_centered_halfspaces n)) hx
end Ehrhart.Geometry
