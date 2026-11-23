-- Prove2me | solution 1 for DiscreteTiling.TileSet.Disjoint.finiteDistinctIntersections
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:58:13.875283+00:00
-- url     : https://prove2.me/submissions/78544d03-4766-4236-adb3-0bc72a44dbdf

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Logic.Equiv.Pairwise
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Theorems.Thm_DiscreteTiling_TileSet_Disjoint_finiteIntersections

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
theorem _root_.solution {t : TileSet ps ιₜ}
    (h : t.Disjoint) : t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (Disjoint.finiteIntersections h)
end Disjoint
end DiscreteTiling.TileSet
