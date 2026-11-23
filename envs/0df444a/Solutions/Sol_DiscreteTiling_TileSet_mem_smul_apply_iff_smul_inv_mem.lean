-- Prove2me | solution 1 for DiscreteTiling.TileSet.mem_smul_apply_iff_smul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:53:05.903447+00:00
-- url     : https://prove2.me/submissions/51b6ee4e-2bb7-48db-9990-05dd3b4dabd9

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
    x ∈ (g • t) i ↔ g⁻¹ • x ∈ t i :=
  PlacedTile.mem_smul_iff_smul_inv_mem
end DiscreteTiling.TileSet
