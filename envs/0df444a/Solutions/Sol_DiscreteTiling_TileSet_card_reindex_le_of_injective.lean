-- Prove2me | solution 1 for DiscreteTiling.TileSet.card_reindex_le_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:56:50.626349+00:00
-- url     : https://prove2.me/submissions/94265756-e499-457f-8dc0-40fce4e690d0

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Theorems.Thm_DiscreteTiling_TileSetCard_le_def
public import Theorems.Thm_DiscreteTiling_TileSet_card_apply

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
theorem _root_.solution (t : TileSet ps ιᵤ) {f : ιᵤ' → ιᵤ} (hf : Injective f) :
    (t.reindex f).card ≤ t.card := by
  simp_rw [TileSetCard.le_def, card_apply, TileSet.coe_reindex, Set.preimage_comp]
  exact fun _ ↦ Cardinal.mk_preimage_of_injective _ _ hf
end DiscreteTiling.TileSet
