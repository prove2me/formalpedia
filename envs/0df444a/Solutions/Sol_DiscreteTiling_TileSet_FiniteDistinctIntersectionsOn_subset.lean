-- Prove2me | solution 1 for DiscreteTiling.TileSet.FiniteDistinctIntersectionsOn.subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:20:33.951092+00:00
-- url     : https://prove2.me/submissions/0caf252f-7668-4b1e-bbe0-89bb5cae9720

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
theorem _root_.solution {s₁ s₂ : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersectionsOn s₂) (hs : s₁ ⊆ s₂) :
    t.FiniteDistinctIntersectionsOn s₁ :=
  fun x hx ↦ hfi x (Set.mem_of_mem_of_subset hx hs)
end FiniteDistinctIntersectionsOn
end DiscreteTiling.TileSet
