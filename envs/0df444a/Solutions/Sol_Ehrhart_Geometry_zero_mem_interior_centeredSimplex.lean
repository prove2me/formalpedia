-- Prove2me | solution 1 for Ehrhart.Geometry.zero_mem_interior_centeredSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/ac84649a-d9cb-4327-b505-b5fdf60c2388

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_mem_interior_centeredSimplex_iff

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
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    (0 : Space n) ∈ interior (centeredSimplex n) := by
  apply (mem_interior_centeredSimplex_iff hn).mpr
  constructor
  · intro i
    simp
  · simp
end Ehrhart.Geometry
