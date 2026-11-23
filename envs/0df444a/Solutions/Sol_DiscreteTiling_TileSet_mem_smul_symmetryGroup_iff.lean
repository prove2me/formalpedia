-- Prove2me | solution 1 for DiscreteTiling.TileSet.mem_smul_symmetryGroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:04:30.962244+00:00
-- url     : https://prove2.me/submissions/0ae62b82-f244-425e-aa44-5b9ffcd9a88b

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
theorem _root_.solution {t : TileSet ps ιₜ} {g : t.symmetryGroup}
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    x ∈ ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔ x ∈ g • (pt : PlacedTile ps) :=
  Iff.rfl
end DiscreteTiling.TileSet
