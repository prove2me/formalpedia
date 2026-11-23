-- Prove2me | solution 1 for DiscreteTiling.TileSet.isohedralNumber_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:09:40.092404+00:00
-- url     : https://prove2.me/submissions/2ea8e616-f6b3-4cf6-86d2-5fdb806caf85

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
theorem _root_.solution {t : TileSet ps ιₜ} :
    t.isohedralNumber ≤ 1 ↔ MulAction.IsPretransitive t.symmetryGroup
    (t : Set (PlacedTile ps)) := by
  rw [isohedralNumber_eq_card, Cardinal.le_one_iff_subsingleton,
      MulAction.pretransitive_iff_subsingleton_quotient]
end DiscreteTiling.TileSet
