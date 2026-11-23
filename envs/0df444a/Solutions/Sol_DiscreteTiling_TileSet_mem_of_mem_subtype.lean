-- Prove2me | solution 1 for DiscreteTiling.TileSet.mem_of_mem_subtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:32.151796+00:00
-- url     : https://prove2.me/submissions/ec1ad264-a44f-4145-9fe4-7ccee7e9a439

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSet_mem_of_mem_reindex


set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ ιₜ' Eᵤ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} {p : ιₜ → Prop} {pt : PlacedTile ps}
    (h : pt ∈ t.subtype p) : pt ∈ t :=
  t.mem_of_mem_reindex h
end DiscreteTiling.TileSet
