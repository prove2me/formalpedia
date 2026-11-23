-- Prove2me | solution 1 for DiscreteTiling.TileSet.isohedralNumberNat_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:22:46.60445+00:00
-- url     : https://prove2.me/submissions/1090cae5-a702-40a0-9128-771dfae1bbfd

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral

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
theorem _root_.solution (t : TileSet ps ιₜ) :
    t.isohedralNumberNat =
      Nat.card (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) :=
  rfl
end DiscreteTiling.TileSet
