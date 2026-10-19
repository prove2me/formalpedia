-- Prove2me | solution 1 for Ehrhart.Geometry.coordinateSum_lt_of_mem_interior_centeredSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/2bf608a3-9d73-4699-b1a4-0d22ae0dc733

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_coordinateSum_surjective
import Theorems.Thm_Ehrhart_Geometry_continuous_coordinateSum
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
theorem _root_.solution
    {n : ℕ} (hn : 0 < n) {x : Space n}
    (hx : x ∈ interior (centeredSimplex n)) :
    (∑ i, x i) < 1 := by
  have hsub : centeredSimplex n ⊆
      (coordinateSum n) ⁻¹' Iic (1 : ℝ) := by
    intro y hy
    exact (mem_centeredSimplex_iff.mp hy).2
  have hi := interior_mono hsub hx
  have hopen : IsOpenMap (coordinateSum n) :=
    (coordinateSum n).isOpenMap_of_finiteDimensional
      (coordinateSum_surjective n hn)
  rw [← hopen.preimage_interior_eq_interior_preimage
    (continuous_coordinateSum n) (Iic (1 : ℝ)), interior_Iic] at hi
  exact hi
end Ehrhart.Geometry
