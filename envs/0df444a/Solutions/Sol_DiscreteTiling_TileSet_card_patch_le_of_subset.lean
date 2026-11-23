-- Prove2me | solution 1 for DiscreteTiling.TileSet.card_patch_le_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:43.023152+00:00
-- url     : https://prove2.me/submissions/415ad4bf-6aae-4a36-a627-8260fb6499f4

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSet_card_patch_le
public import Theorems.Thm_DiscreteTiling_TileSet_patch_patch_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_card_reindex_of_equivLike
attribute [local simp] DiscreteTiling.TileSet.card_reindex_of_equivLike



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
theorem _root_.solution (t : TileSet ps ιₜ) {s₁ s₂ : Set X} (h : s₂ ⊆ s₁) :
    (t.patch s₂).card ≤ (t.patch s₁).card := by
  rw [← card_reindex_of_equivLike _ (t.patchPatchEquiv h), t.patch_patch_reindex h]
  exact card_patch_le _ _
end DiscreteTiling.TileSet
