-- Prove2me | solution 1 for DiscreteTiling.TileSet.Disjoint.finiteIntersections
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:57:35.276845+00:00
-- url     : https://prove2.me/submissions/17a479a7-8134-406b-98eb-59cb5facf53f

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
theorem _root_.solution {t : TileSet ps ιₜ} (h : t.Disjoint) :
    t.FiniteIntersections :=
  fun _ ↦ Set.Subsingleton.finite (subsingleton_setOfPred_mem_iff_pairwise_disjoint.2 h _)
end Disjoint
end DiscreteTiling.TileSet
