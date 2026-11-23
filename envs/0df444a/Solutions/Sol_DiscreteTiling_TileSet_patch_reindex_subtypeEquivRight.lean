-- Prove2me | solution 1 for DiscreteTiling.TileSet.patch_reindex_subtypeEquivRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:11.079787+00:00
-- url     : https://prove2.me/submissions/c43d4731-88d9-42f3-b0af-7ab918bf7d7b

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSet_reindex_subtypeEquivRight

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
theorem _root_.solution (t : TileSet ps ιₜ) {s₁ s₂ : Set X}
    (h : ∀ i, (s₂ ∩ t i).Nonempty ↔ (s₁ ∩ t i).Nonempty) :
    (t.patch s₁).reindex (Equiv.subtypeEquivRight h) = t.patch s₂ :=
  t.reindex_subtypeEquivRight h
end DiscreteTiling.TileSet
