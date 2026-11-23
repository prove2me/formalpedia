-- Prove2me | solution 1 for DiscreteTiling.TileSet.mem_of_mem_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:53:05.467549+00:00
-- url     : https://prove2.me/submissions/34a35f18-010e-4a65-a6b6-1a48b53927aa

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_reindex_subset

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ι ιₜ ιₜ' ιₜ'' ιₜ''' E E' F : Type*} {ιₜι ιₜ'ι : ι → Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
open DiscreteTiling.TileSet
attribute [coe] tiles
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps}
    (h : pt ∈ t.reindex f) : pt ∈ t :=
  Set.mem_of_mem_of_subset h <| t.coeSet_reindex_subset f
end DiscreteTiling.TileSet
