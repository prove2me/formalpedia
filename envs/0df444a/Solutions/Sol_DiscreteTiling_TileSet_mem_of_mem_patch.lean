-- Prove2me | solution 1 for DiscreteTiling.TileSet.mem_of_mem_patch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:15.262536+00:00
-- url     : https://prove2.me/submissions/93b83526-7a6e-4237-9f2a-ced36fd6802d

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSet_mem_of_mem_subtype

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
theorem _root_.solution {t : TileSet ps ιₜ} {s : Set X} {pt : PlacedTile ps} (h : pt ∈ t.patch s) :
    pt ∈ t :=
  t.mem_of_mem_subtype h
end DiscreteTiling.TileSet
