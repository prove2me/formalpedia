-- Prove2me | solution 1 for DiscreteTiling.TileSet.Disjoint.disjointOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:19:47.177796+00:00
-- url     : https://prove2.me/submissions/f12cf35c-d1f3-44e3-8922-d00d0ce6bc67

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
namespace Disjoint
theorem _root_.solution (s : Set X) {t : TileSet ps ιₜ} (hd : t.Disjoint) :
    t.DisjointOn s :=
  fun _ _ h ↦ ((hd h).inter_left _).inter_right _
end Disjoint
end DiscreteTiling.TileSet
