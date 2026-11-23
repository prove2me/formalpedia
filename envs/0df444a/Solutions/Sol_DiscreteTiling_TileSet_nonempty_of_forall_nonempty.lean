-- Prove2me | solution 1 for DiscreteTiling.TileSet.nonempty_of_forall_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:53:36.969075+00:00
-- url     : https://prove2.me/submissions/dcbdaab1-c511-424e-b403-a0e488c5e23b

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Theorems.Thm_DiscreteTiling_TileSet_nonempty_apply_of_forall_nonempty

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
    {pt : PlacedTile ps} (hpt : pt ∈ t) : (pt : Set X).Nonempty := by
  rcases hpt with ⟨i, rfl⟩
  exact t.nonempty_apply_of_forall_nonempty h _
end DiscreteTiling.TileSet
