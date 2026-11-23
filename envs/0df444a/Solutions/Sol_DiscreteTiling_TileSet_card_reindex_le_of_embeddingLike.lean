-- Prove2me | solution 1 for DiscreteTiling.TileSet.card_reindex_le_of_embeddingLike
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:20:40.221502+00:00
-- url     : https://prove2.me/submissions/8abd36f1-b996-4080-899d-c459494ef3ec

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Theorems.Thm_DiscreteTiling_TileSet_card_reindex_le_of_injective

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ E F : Type*}
universe u v
variable {ιᵤ ιᵤ' : Type u} [EquivLike E ιᵤ' ιᵤ] [FunLike F ιᵤ' ιᵤ] [EmbeddingLike F ιᵤ' ιᵤ]
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution (t : TileSet ps ιᵤ) (f : F) : (t.reindex f).card ≤ t.card :=
  t.card_reindex_le_of_injective (EmbeddingLike.injective f)
end DiscreteTiling.TileSet
