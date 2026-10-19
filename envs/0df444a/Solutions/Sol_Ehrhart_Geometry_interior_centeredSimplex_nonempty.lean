-- Prove2me | solution 1 for Ehrhart.Geometry.interior_centeredSimplex_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/582b4342-7a0a-44c2-8493-1aeb6fa786b1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_zero_mem_interior_centeredSimplex

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
    (interior (centeredSimplex n)).Nonempty :=
  ⟨0, zero_mem_interior_centeredSimplex n hn⟩
end Ehrhart.Geometry
