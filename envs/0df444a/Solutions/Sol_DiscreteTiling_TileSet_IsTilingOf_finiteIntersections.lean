-- Prove2me | solution 1 for DiscreteTiling.TileSet.IsTilingOf.finiteIntersections
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:01:03.070206+00:00
-- url     : https://prove2.me/submissions/e2a49898-bada-40d6-896d-fa193edb2297

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Theorems.Thm_DiscreteTiling_TileSet_IsTilingOf_disjoint
public import Theorems.Thm_DiscreteTiling_TileSet_IsTiling_disjoint
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
theorem _root_.solution {t : TileSet ps ιₜ} {s : Set X} (h : t.IsTilingOf s) :
    t.FiniteIntersections :=
  Disjoint.finiteIntersections (IsTilingOf.disjoint h)
end IsTilingOf
end DiscreteTiling.TileSet
