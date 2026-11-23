-- Prove2me | solution 1 for DiscreteTiling.TileSet.DisjointOn.reindex_of_embeddingLike
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:19:43.233674+00:00
-- url     : https://prove2.me/submissions/dee6b6eb-f4bf-4a34-8d93-64ce61827a96

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
namespace DisjointOn
theorem _root_.solution {s : Set X} {t : TileSet ps ιₜ}
    (hd : t.DisjointOn s) (e : F) : (t.reindex e).DisjointOn s :=
  EmbeddingLike.pairwise_comp e hd
end DisjointOn
end DiscreteTiling.TileSet
