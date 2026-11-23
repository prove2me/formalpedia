-- Prove2me | solution 1 for DiscreteTiling.TileSet.injective_reindex_of_embeddingLike
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:53:41.057821+00:00
-- url     : https://prove2.me/submissions/39141223-aab9-4a05-9a6e-1b95134134c6

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
theorem _root_.solution {t : TileSet ps ιₜ} (f : F) (ht : Injective t) :
    Injective (t.reindex f) :=
  (injective_reindex_iff_injective ht).2 <| EmbeddingLike.injective f
end DiscreteTiling.TileSet
