-- Prove2me | solution 1 for DiscreteTiling.TileSet.Disjoint.reindex_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:57:42.199875+00:00
-- url     : https://prove2.me/submissions/ed5be82a-5df2-48e3-826e-905bb86ce2fe

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
theorem _root_.solution {t : TileSet ps ιₜ} (hd : t.Disjoint) {e : ιₜ' → ιₜ}
    (h : Injective e) : (t.reindex e).Disjoint :=
  hd.comp_of_injective h
end Disjoint
end DiscreteTiling.TileSet
