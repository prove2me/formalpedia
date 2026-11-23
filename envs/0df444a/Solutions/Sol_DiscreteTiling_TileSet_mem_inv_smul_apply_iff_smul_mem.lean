-- Prove2me | solution 1 for DiscreteTiling.TileSet.mem_inv_smul_apply_iff_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:53:44.709089+00:00
-- url     : https://prove2.me/submissions/a0e1bb40-9eba-42a0-b02d-28761d34aa86

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
theorem _root_.solution {g : G} {x : X} {t : TileSet ps ιₜ} {i : ιₜ} :
    x ∈ (g⁻¹ • t) i ↔ g • x ∈ t i :=
  PlacedTile.mem_inv_smul_iff_smul_mem
end DiscreteTiling.TileSet
