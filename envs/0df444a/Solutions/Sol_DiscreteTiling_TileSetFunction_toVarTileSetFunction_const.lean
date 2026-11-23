-- Prove2me | solution 1 for DiscreteTiling.TileSetFunction.toVarTileSetFunction_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:55:41.932188+00:00
-- url     : https://prove2.me/submissions/61f2845f-220f-42d2-8e68-78f0b97f2493

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
variable (Y ps H)
namespace DiscreteTiling.TileSetFunction
theorem _root_.solution (a : α) :
    (TileSetFunction.const ps H a).toVarTileSetFunction Y = VarTileSetFunction.const Y ps H a :=
  rfl
end DiscreteTiling.TileSetFunction
