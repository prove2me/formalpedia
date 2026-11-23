-- Prove2me | solution 1 for DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:55:42.441284+00:00
-- url     : https://prove2.me/submissions/2da4d1d8-b385-47f8-be88-5a6cf0a3c700

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X Y ιₚ : Type*} [Group G] [MulAction G X] [MulAction G Y]
universe u
variable {ps : Protoset G X ιₚ} {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' Eᵤ α β γ : Type*}
variable {H : Subgroup G}
variable [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSetFunction
namespace DiscreteTiling.TileSetFunction
theorem _root_.solution (f : TileSetFunction ps α H) (y : Y) :
    (f.toVarTileSetFunction Y).toTileSetFunction y = f.ofLE inf_le_left :=
  rfl
end DiscreteTiling.TileSetFunction
