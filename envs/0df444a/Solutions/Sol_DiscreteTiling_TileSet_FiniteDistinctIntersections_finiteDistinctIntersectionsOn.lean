-- Prove2me | solution 1 for DiscreteTiling.TileSet.FiniteDistinctIntersections.finiteDistinctIntersectionsOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:02:09.300798+00:00
-- url     : https://prove2.me/submissions/d76bac24-07ef-4e13-9a58-ce5b20da5ade

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
theorem _root_.solution (s : Set X) {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersections) : t.FiniteDistinctIntersectionsOn s :=
  fun _ _ ↦ hfi _
end FiniteDistinctIntersections
end DiscreteTiling.TileSet
