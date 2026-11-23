-- Prove2me | solution 1 for DiscreteTiling.TileSet.reindex_subtypeEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:02.124343+00:00
-- url     : https://prove2.me/submissions/92442a89-6f83-42e7-be64-67b98981b6ff

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
theorem _root_.solution (t : TileSet ps ιₜ) {p : ιₜ → Prop} {e : ιₜ' ≃ ιₜ} {q : ιₜ' → Prop}
    (h : ∀ i, q i ↔ p (e i)) :
    (t.subtype p).reindex (Equiv.subtypeEquiv e h) = (t.reindex e).subtype q :=
  rfl
end DiscreteTiling.TileSet
