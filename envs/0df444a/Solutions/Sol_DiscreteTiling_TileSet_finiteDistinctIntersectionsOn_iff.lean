-- Prove2me | solution 1 for DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:20:29.497307+00:00
-- url     : https://prove2.me/submissions/3153afa5-4550-44a4-9f6b-efa5ce428b4d

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
theorem _root_.solution {s : Set X} {t : TileSet ps ιₜ} :
    t.FiniteDistinctIntersectionsOn s ↔ ∀ x ∈ s, {pt | pt ∈ t ∧ x ∈ pt}.Finite :=
  Iff.rfl
end DiscreteTiling.TileSet
