-- Prove2me | solution 1 for DiscreteTiling.TileSet.FiniteDistinctIntersections.reindex_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:20:29.055404+00:00
-- url     : https://prove2.me/submissions/e1ffd667-f955-4eea-a81e-83488b3917e7

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
namespace FiniteDistinctIntersections
theorem _root_.solution {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteDistinctIntersections) (h : Surjective e) :
    t.FiniteDistinctIntersections := by
  intro x
  convert hfi x using 4
  exact (mem_reindex_iff_of_surjective h).symm
end FiniteDistinctIntersections
end DiscreteTiling.TileSet
