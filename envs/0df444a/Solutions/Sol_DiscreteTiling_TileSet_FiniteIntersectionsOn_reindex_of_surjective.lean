-- Prove2me | solution 1 for DiscreteTiling.TileSet.FiniteIntersectionsOn.reindex_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:20:18.594922+00:00
-- url     : https://prove2.me/submissions/5d89b4ad-32a6-40bc-8558-45fa3a70a1b3

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
theorem _root_.solution {s : Set X} {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteIntersectionsOn s) (h : Surjective e) :
    t.FiniteIntersectionsOn s :=
  fun x hx ↦ Set.Finite.of_preimage (hfi x hx) h
end FiniteIntersectionsOn
end DiscreteTiling.TileSet
