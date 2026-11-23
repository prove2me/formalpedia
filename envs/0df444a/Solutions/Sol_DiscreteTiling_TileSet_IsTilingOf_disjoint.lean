-- Prove2me | solution 1 for DiscreteTiling.TileSet.IsTilingOf.disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:59:08.67371+00:00
-- url     : https://prove2.me/submissions/ddc60c8c-ceca-471e-9cfb-8ab5f9daa306

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling

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
    t.Disjoint :=
  And.left h
end IsTilingOf
end DiscreteTiling.TileSet
