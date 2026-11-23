-- Prove2me | solution 1 for DiscreteTiling.TileSet.isohedralNumber_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:05:31.871839+00:00
-- url     : https://prove2.me/submissions/1c2c7618-269e-4c74-a97b-762b4a55f8f6

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_eq_card

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
theorem _root_.solution (t : TileSet ps ιₜ) : t.isohedralNumber ≠ 0 ↔ Nonempty ιₜ := by
  rw [isohedralNumber_eq_card, Cardinal.mk_ne_zero_iff, nonempty_quotient_iff,
      Set.nonempty_coe_sort, coeSet_apply, Set.range_nonempty_iff_nonempty]
end DiscreteTiling.TileSet
