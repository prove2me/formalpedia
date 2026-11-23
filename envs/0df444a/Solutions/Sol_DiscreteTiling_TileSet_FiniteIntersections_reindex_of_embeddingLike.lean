-- Prove2me | solution 1 for DiscreteTiling.TileSet.FiniteIntersections.reindex_of_embeddingLike
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:19:50.36622+00:00
-- url     : https://prove2.me/submissions/76164172-62c6-4953-a62f-0f2fb1c96a99

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Logic.Equiv.Pairwise
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Theorems.Thm_DiscreteTiling_TileSet_Disjoint_reindex_of_injective
public import Theorems.Thm_DiscreteTiling_TileSet_DisjointOn_reindex_of_injective
public import Theorems.Thm_DiscreteTiling_TileSet_FiniteIntersections_reindex_of_injective

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
theorem _root_.solution {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) (e : F) : (t.reindex e).FiniteIntersections :=
  FiniteIntersections.reindex_of_injective hfi (EmbeddingLike.injective _)
end FiniteIntersections
end DiscreteTiling.TileSet
