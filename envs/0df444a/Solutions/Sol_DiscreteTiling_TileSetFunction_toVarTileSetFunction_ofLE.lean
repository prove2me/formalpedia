-- Prove2me | solution 1 for DiscreteTiling.TileSetFunction.toVarTileSetFunction_ofLE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:19:22.045798+00:00
-- url     : https://prove2.me/submissions/78e44a9a-9c7a-4aaf-952d-977147c7649a

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
variable (Y)
namespace DiscreteTiling.TileSetFunction
theorem _root_.solution (f : TileSetFunction ps α H) {H' : Subgroup G} (h : H' ≤ H) :
    (f.ofLE h).toVarTileSetFunction Y = (f.toVarTileSetFunction Y).ofLE h :=
  rfl
end DiscreteTiling.TileSetFunction
