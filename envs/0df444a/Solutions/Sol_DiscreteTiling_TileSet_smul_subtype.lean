-- Prove2me | solution 1 for DiscreteTiling.TileSet.smul_subtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:05.006701+00:00
-- url     : https://prove2.me/submissions/b2a704a6-e603-48b5-846c-a8c43cfc2732

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ ιₜ' Eᵤ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution (g : G) (t : TileSet ps ιₜ) (p : ιₜ → Prop) :
    g • (t.subtype p) = (g • t).subtype p :=
  t.smul_reindex _ _
end DiscreteTiling.TileSet
