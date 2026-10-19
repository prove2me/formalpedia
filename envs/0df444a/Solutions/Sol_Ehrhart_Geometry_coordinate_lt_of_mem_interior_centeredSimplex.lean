-- Prove2me | solution 1 for Ehrhart.Geometry.coordinate_lt_of_mem_interior_centeredSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/ae4087d8-a62d-4521-8e95-b9977e6ce51e

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
theorem _root_.solution
    {n : ℕ} {x : Space n}
    (hx : x ∈ interior (centeredSimplex n)) (i : Fin n) :
    -(1 : ℝ) < x i := by
  have hsub : centeredSimplex n ⊆
      (fun y : Space n => y i) ⁻¹' Ici (-(1 : ℝ)) := by
    intro y hy
    exact (mem_centeredSimplex_iff.mp hy).1 i
  have hi := interior_mono hsub hx
  have hopen : IsOpenMap (fun y : Space n => y i) :=
    isOpenMap_eval i
  rw [← hopen.preimage_interior_eq_interior_preimage
    (continuous_apply i) (Ici (-(1 : ℝ))), interior_Ici] at hi
  exact hi
end Ehrhart.Geometry
