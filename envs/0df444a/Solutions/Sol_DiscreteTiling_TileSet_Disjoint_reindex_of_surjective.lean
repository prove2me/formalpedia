-- Prove2me | solution 1 for DiscreteTiling.TileSet.Disjoint.reindex_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:19:42.724749+00:00
-- url     : https://prove2.me/submissions/a0ea81da-8626-411b-812d-f0a777b22de2

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
theorem _root_.solution {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hd : (t.reindex e).Disjoint) (h : Surjective e) : t.Disjoint :=
  Pairwise.of_comp_of_surjective hd h
end Disjoint
end DiscreteTiling.TileSet
