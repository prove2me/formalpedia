-- Prove2me | solution 1 for DiscreteTiling.TileSet.mem_symmetryGroup_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:52:01.880887+00:00
-- url     : https://prove2.me/submissions/aa6f5e9f-c15e-44a1-900c-146af98b53dc

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl

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
theorem _root_.solution {t : TileSet ps ιₜ} {g : G} :
    g ∈ t.symmetryGroup ↔ ∃ f : Equiv.Perm ιₜ, (g • t).reindex f = t := by
  simp_rw [symmetryGroup, Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  change (∃ x : G × Equiv.Perm ιₜ, _ ∧ x.1 = g) ↔ _
  refine ⟨fun ⟨⟨g', f⟩, ⟨h, hg⟩⟩ ↦ ⟨f.symm, ?_⟩, fun ⟨f, h⟩ ↦ ⟨(g, f.symm), h, rfl⟩⟩
  dsimp only at hg
  subst hg
  exact h
end DiscreteTiling.TileSet
