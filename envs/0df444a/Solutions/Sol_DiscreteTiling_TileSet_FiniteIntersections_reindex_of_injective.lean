-- Prove2me | solution 1 for DiscreteTiling.TileSet.FiniteIntersections.reindex_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:57:40.509447+00:00
-- url     : https://prove2.me/submissions/5ad7fd3d-99b5-4396-95ad-d9503251e391

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
theorem _root_.solution {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) {e : ιₜ' → ιₜ} (h : Injective e) :
    (t.reindex e).FiniteIntersections :=
  fun x ↦ Set.Finite.preimage (Set.injOn_of_injective h) (hfi x)
end FiniteIntersections
end DiscreteTiling.TileSet
