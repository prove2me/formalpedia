-- Prove2me | solution 1 for DiscreteTiling.TileSet.card_reindex_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:08:41.737504+00:00
-- url     : https://prove2.me/submissions/4f4b155b-93f3-4d2f-a5d2-9e0b4d95d6f6

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Theorems.Thm_DiscreteTiling_TileSet_card_reindex_le_of_injective
public import Theorems.Thm_DiscreteTiling_TileSet_card_le_card_reindex_of_surjective

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
theorem _root_.solution (t : TileSet ps ιᵤ) {f : ιᵤ' → ιᵤ} (hf : Bijective f) :
    (t.reindex f).card = t.card :=
  le_antisymm (t.card_reindex_le_of_injective hf.injective)
              (t.card_le_card_reindex_of_surjective hf.surjective)
end DiscreteTiling.TileSet
