-- Prove2me | solution 1 for DiscreteTiling.TileSet.card_eq_iff_exists_reindex_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:20:47.147108+00:00
-- url     : https://prove2.me/submissions/8969266d-bbbf-498f-a633-4597d6c67a7a

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Theorems.Thm_DiscreteTiling_TileSet_card_apply
public import Theorems.Thm_DiscreteTiling_TileSet_card_reindex_of_equivLike
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.coeSet_sigma
attribute [local simp] DiscreteTiling.TileSet.coeSet_sum
attribute [local simp] DiscreteTiling.TileSet.coe_sigma
attribute [local simp] DiscreteTiling.TileSet.coe_sum
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective


attribute [local simp] DiscreteTiling.TileSet.card_reindex_of_equivLike

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
theorem _root_.solution {t₁ : TileSet ps ιᵤ} {t₂ : TileSet ps ιᵤ'} :
    t₁.card = t₂.card ↔ ∃ e : ιᵤ' ≃ ιᵤ, t₁.reindex e = t₂ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simp_rw [TileSetCard.ext_iff, funext_iff, card_apply, Cardinal.eq] at h
    refine ⟨Equiv.ofPreimageEquiv fun pt ↦ (h pt).some.symm, ?_⟩
    simp_rw [TileSet.ext_iff, funext_iff, reindex_apply, Equiv.ofPreimageEquiv_map, implies_true]
  · rintro ⟨e, rfl⟩
    rw [card_reindex_of_equivLike]
end DiscreteTiling.TileSet
