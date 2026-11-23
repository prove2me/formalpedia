-- Prove2me | solution 1 for DiscreteTiling.TileSet.IsTilingOf.finiteDistinctIntersections
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:03:02.123112+00:00
-- url     : https://prove2.me/submissions/885ef629-dffa-4031-aa74-ba1fe1581cc6

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Theorems.Thm_DiscreteTiling_TileSet_IsTilingOf_finiteIntersections
public import Theorems.Thm_DiscreteTiling_TileSet_IsTiling_finiteIntersections
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
namespace IsTilingOf
theorem _root_.solution {t : TileSet ps ιₜ} {s : Set X}
    (h : t.IsTilingOf s) : t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (IsTilingOf.finiteIntersections h)
end IsTilingOf
end DiscreteTiling.TileSet
