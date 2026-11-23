-- Prove2me | solution 1 for DiscreteTiling.TileSet.IsTiling.finiteIntersections
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:01:53.958056+00:00
-- url     : https://prove2.me/submissions/df91f41b-e9da-4d8e-8416-100b48de7c0a

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Theorems.Thm_DiscreteTiling_TileSet_IsTilingOf_disjoint
public import Theorems.Thm_DiscreteTiling_TileSet_IsTiling_disjoint
public import Theorems.Thm_DiscreteTiling_TileSet_IsTilingOf_finiteIntersections
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
theorem _root_.solution {t : TileSet ps ιₜ} (h : t.IsTiling) :
    t.FiniteIntersections :=
  Disjoint.finiteIntersections (IsTiling.disjoint h)
end IsTiling
end DiscreteTiling.TileSet
