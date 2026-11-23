-- Prove2me | solution 1 for DiscreteTiling.TileSet.nonempty_apply_of_forall_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:52:31.139573+00:00
-- url     : https://prove2.me/submissions/d80312bc-b8c5-4146-8eb4-4778fcae92b0

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
theorem _root_.solution (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Nonempty)
    (i : ιₜ) : (t i : Set X).Nonempty :=
  PlacedTile.coe_nonempty_iff.2 (h _)
end DiscreteTiling.TileSet
