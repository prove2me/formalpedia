-- Prove2me | solution 1 for DiscreteTiling.TileSet.mem_smul_iff_smul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:52:13.624177+00:00
-- url     : https://prove2.me/submissions/572328df-d067-4fa9-975a-54dee021d94b

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
theorem _root_.solution {pt : PlacedTile ps} {g : G} {t : TileSet ps ιₜ} :
    pt ∈ g • t ↔ g⁻¹ • pt ∈ t := by
  simp_rw [← mem_coeSet, coeSet_smul, Set.mem_smul_set_iff_inv_smul_mem]
end DiscreteTiling.TileSet
