-- Prove2me | solution 1 for DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:53:43.07534+00:00
-- url     : https://prove2.me/submissions/15590fce-2f3d-4eb2-8c39-5eae049652cb

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex

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
theorem _root_.solution (t : TileSet ps ιₜ) {f : ιₜ' → ιₜ}
    (h : Bijective f) : (t.reindex f).symmetryGroup = t.symmetryGroup :=
  t.symmetryGroup_reindex <| Equiv.ofBijective f h
end DiscreteTiling.TileSet
