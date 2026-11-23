-- Prove2me | solution 1 for DiscreteTiling.TileSet.patch_patch_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:16:47.758041+00:00
-- url     : https://prove2.me/submissions/0a893b11-e3ed-4c97-8e10-3330b85dc9e6

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ ιₜ' Eᵤ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution (t : TileSet ps ιₜ) {s₁ s₂ : Set X} (h : s₂ ⊆ s₁) :
    (t.patch s₂).reindex (t.patchPatchEquiv h) = (t.patch s₁).patch s₂ :=
  rfl
end DiscreteTiling.TileSet
