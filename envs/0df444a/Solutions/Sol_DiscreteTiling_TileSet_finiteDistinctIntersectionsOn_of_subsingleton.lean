-- Prove2me | solution 1 for DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:58:42.596278+00:00
-- url     : https://prove2.me/submissions/3efc4fdf-1c80-4fad-be14-011da9be80e5

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Logic.Equiv.Pairwise
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
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
theorem _root_.solution [Subsingleton ιₜ] (s : Set X)
    (t : TileSet ps ιₜ) : t.FiniteDistinctIntersectionsOn s :=
  FiniteIntersectionsOn.finiteDistinctIntersectionsOn (finiteIntersectionsOn_of_subsingleton s t)
end DiscreteTiling.TileSet
