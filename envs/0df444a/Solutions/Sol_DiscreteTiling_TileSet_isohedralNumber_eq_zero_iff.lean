-- Prove2me | solution 1 for DiscreteTiling.TileSet.isohedralNumber_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:06:29.565632+00:00
-- url     : https://prove2.me/submissions/f3f4947b-213d-45b3-91c4-983c740148c8

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_ne_zero_iff

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution (t : TileSet ps ιₜ) : t.isohedralNumber = 0 ↔ IsEmpty ιₜ := by
  rw [← not_iff_not, not_isEmpty_iff]
  exact t.isohedralNumber_ne_zero_iff
end DiscreteTiling.TileSet
