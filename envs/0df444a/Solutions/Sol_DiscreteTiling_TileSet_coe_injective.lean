-- Prove2me | solution 1 for DiscreteTiling.TileSet.coe_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:52:07.402794+00:00
-- url     : https://prove2.me/submissions/98e8e702-4e98-4517-8d54-ea7a70783c8e

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet

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
theorem _root_.solution : Injective (TileSet.tiles : TileSet ps ιₜ → ιₜ → PlacedTile ps) :=
  fun _ _ ↦ coe_inj.1
end DiscreteTiling.TileSet
