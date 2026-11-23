-- Prove2me | solution 1 for DiscreteTiling.TileSet.injective_subtype_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:11.115287+00:00
-- url     : https://prove2.me/submissions/b4d5f3af-39a2-47a1-9251-82f26f9b8620

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
theorem _root_.solution {t : TileSet ps ιₜ} (p : ιₜ → Prop) (ht : Injective t) :
    Injective (t.subtype p) :=
  (injective_reindex_iff_injective ht).2 Subtype.val_injective
end DiscreteTiling.TileSet
