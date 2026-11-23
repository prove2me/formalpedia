-- Prove2me | solution 1 for DiscreteTiling.TileSet.exists_smul_eq_of_mem_of_mem_symmetryGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:53:52.854897+00:00
-- url     : https://prove2.me/submissions/ef1b740e-e3e3-4604-bada-0e9ad3a1a4dd

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Theorems.Thm_P2M_DiscreteTiling_TileSet_exists_smul_eq_of_mem_symmetryGroup__3557f4183e3f

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
theorem _root_.solution {t : TileSet ps ιₜ} {g : G} {pt : PlacedTile ps}
    (hg : g ∈ t.symmetryGroup) (hpt : pt ∈ t) : ∃ pt' ∈ t, g • pt' = pt := by
  rcases hpt with ⟨i, rfl⟩
  rw [exists_mem_iff]
  exact exists_smul_eq_of_mem_symmetryGroup' i hg
end DiscreteTiling.TileSet
