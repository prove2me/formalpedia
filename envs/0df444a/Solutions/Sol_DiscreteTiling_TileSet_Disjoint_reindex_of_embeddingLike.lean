-- Prove2me | solution 1 for DiscreteTiling.TileSet.Disjoint.reindex_of_embeddingLike
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:19:35.49657+00:00
-- url     : https://prove2.me/submissions/7b261adf-f03d-4860-a55d-80a929d4dfda

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
theorem _root_.solution {t : TileSet ps ιₜ} (hd : t.Disjoint) (e : F) :
    (t.reindex e).Disjoint :=
  EmbeddingLike.pairwise_comp e hd
end Disjoint
end DiscreteTiling.TileSet
