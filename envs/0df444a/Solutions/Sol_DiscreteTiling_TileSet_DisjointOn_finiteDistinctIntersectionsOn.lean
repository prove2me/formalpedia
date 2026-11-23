-- Prove2me | solution 1 for DiscreteTiling.TileSet.DisjointOn.finiteDistinctIntersectionsOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:02:19.900428+00:00
-- url     : https://prove2.me/submissions/57da62c6-5504-48a1-b39a-801aa688af95

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Logic.Equiv.Pairwise
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Theorems.Thm_DiscreteTiling_TileSet_DisjointOn_finiteIntersectionsOn
public import Theorems.Thm_DiscreteTiling_TileSet_FiniteIntersections_finiteIntersectionsOn
public import Theorems.Thm_DiscreteTiling_TileSet_FiniteIntersectionsOn_finiteDistinctIntersectionsOn

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
namespace DisjointOn
theorem _root_.solution {s : Set X} {t : TileSet ps ιₜ}
    (h : t.DisjointOn s) : t.FiniteDistinctIntersectionsOn s :=
  FiniteIntersectionsOn.finiteDistinctIntersectionsOn (DisjointOn.finiteIntersectionsOn h)
end DisjointOn
end DiscreteTiling.TileSet
