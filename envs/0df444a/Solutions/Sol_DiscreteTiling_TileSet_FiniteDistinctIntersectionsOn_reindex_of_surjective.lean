-- Prove2me | solution 1 for DiscreteTiling.TileSet.FiniteDistinctIntersectionsOn.reindex_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:20:33.450724+00:00
-- url     : https://prove2.me/submissions/bc8eb9dd-c003-406f-ad2e-3643e5e4568b

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
namespace FiniteDistinctIntersectionsOn
theorem _root_.solution {s : Set X} {t : TileSet ps ιₜ}
    {e : ιₜ' → ιₜ} (hfi : (t.reindex e).FiniteDistinctIntersectionsOn s) (h : Surjective e) :
    t.FiniteDistinctIntersectionsOn s := by
  intro x
  convert hfi x using 5
  exact (mem_reindex_iff_of_surjective h).symm
end FiniteDistinctIntersectionsOn
end DiscreteTiling.TileSet
