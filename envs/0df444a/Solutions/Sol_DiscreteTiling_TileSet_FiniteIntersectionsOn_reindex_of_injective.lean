-- Prove2me | solution 1 for DiscreteTiling.TileSet.FiniteIntersectionsOn.reindex_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:58:07.606425+00:00
-- url     : https://prove2.me/submissions/9a4f7145-8ba1-4424-a319-93d3073cddb6

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Logic.Equiv.Pairwise
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' F : Type*}
variable [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
namespace FiniteIntersectionsOn
theorem _root_.solution {s : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersectionsOn s) {e : ιₜ' → ιₜ} (h : Injective e) :
    (t.reindex e).FiniteIntersectionsOn s :=
  fun x hx ↦ Set.Finite.preimage (Set.injOn_of_injective h) (hfi x hx)
end FiniteIntersectionsOn
end DiscreteTiling.TileSet
