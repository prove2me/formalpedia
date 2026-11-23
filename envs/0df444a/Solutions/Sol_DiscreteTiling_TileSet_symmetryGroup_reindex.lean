-- Prove2me | solution 1 for DiscreteTiling.TileSet.symmetryGroup_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:53:07.469802+00:00
-- url     : https://prove2.me/submissions/4636e3be-54a1-4c0f-8a61-0dfddb855e52

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_mem_symmetryGroup_iff_exists
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty

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
theorem _root_.solution (t : TileSet ps ιₜ) (f : E) :
    (t.reindex f).symmetryGroup = t.symmetryGroup := by
  ext g
  simp_rw [mem_symmetryGroup_iff_exists]
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · refine ⟨((EquivLike.toEquiv f).symm.trans e).trans (EquivLike.toEquiv f), ?_⟩
    rw [← reindex_eq_reindex_iff_of_equivLike f, ← he]
    simp [comp_assoc]
  · refine ⟨((EquivLike.toEquiv f).trans e).trans (EquivLike.toEquiv f).symm, ?_⟩
    nth_rewrite 2 [← he]
    simp [← comp_assoc]
end DiscreteTiling.TileSet
