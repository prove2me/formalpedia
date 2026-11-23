-- Prove2me | solution 1 for DiscreteTiling.TileSet.IsTiling.finiteDistinctIntersections
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:04:43.544583+00:00
-- url     : https://prove2.me/submissions/120e887e-f4a3-4654-a9b7-7533d9e213f9

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Theorems.Thm_DiscreteTiling_TileSet_IsTilingOf_finiteIntersections
public import Theorems.Thm_DiscreteTiling_TileSet_IsTiling_finiteIntersections
public import Theorems.Thm_DiscreteTiling_TileSet_IsTilingOf_finiteDistinctIntersections
public import Theorems.Thm_DiscreteTiling_TileSet_Disjoint_finiteDistinctIntersections
public import Theorems.Thm_DiscreteTiling_TileSet_Disjoint_finiteIntersections


set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
namespace IsTiling
theorem _root_.solution {t : TileSet ps ιₜ}
    (h : t.IsTiling) : t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (IsTiling.finiteIntersections h)
end IsTiling
end DiscreteTiling.TileSet
