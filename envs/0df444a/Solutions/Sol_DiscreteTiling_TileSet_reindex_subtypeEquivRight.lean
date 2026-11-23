-- Prove2me | solution 1 for DiscreteTiling.TileSet.reindex_subtypeEquivRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:24.208904+00:00
-- url     : https://prove2.me/submissions/ff6ff9bd-33c1-444d-a10b-38da8cc13506

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
theorem _root_.solution (t : TileSet ps ιₜ) {p q : ιₜ → Prop} (h : ∀ i, q i ↔ p i) :
    (t.subtype p).reindex (Equiv.subtypeEquivRight h) = t.subtype q :=
  rfl
end DiscreteTiling.TileSet
