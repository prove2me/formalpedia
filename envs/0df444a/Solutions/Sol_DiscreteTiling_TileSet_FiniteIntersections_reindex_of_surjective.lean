-- Prove2me | solution 1 for DiscreteTiling.TileSet.FiniteIntersections.reindex_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:19:53.361225+00:00
-- url     : https://prove2.me/submissions/a732f5de-b06d-4da5-ae41-dc7f13cb17fa

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
namespace FiniteIntersections
theorem _root_.solution {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteIntersections) (h : Surjective e) :
    t.FiniteIntersections :=
  fun x ↦ Set.Finite.of_preimage (hfi x) h
end FiniteIntersections
end DiscreteTiling.TileSet
