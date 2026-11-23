-- Prove2me | solution 1 for DiscreteTiling.TileSet.smul_mem_of_mem_of_mem_symmetryGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:53:17.934048+00:00
-- url     : https://prove2.me/submissions/a256a984-f43d-442d-a3dc-71afed74e26f

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Theorems.Thm_DiscreteTiling_TileSet_mem_def
public import Theorems.Thm_DiscreteTiling_TileSet_exists_smul_eq_of_mem_symmetryGroup

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
    (hg : g ∈ t.symmetryGroup) (hpt : pt ∈ t) : g • pt ∈ t := by
  rcases hpt with ⟨i, rfl⟩
  simp_rw [TileSet.mem_def, eq_comm]
  exact exists_smul_eq_of_mem_symmetryGroup i hg
end DiscreteTiling.TileSet
