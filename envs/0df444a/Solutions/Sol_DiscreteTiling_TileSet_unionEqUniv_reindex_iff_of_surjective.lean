-- Prove2me | solution 1 for DiscreteTiling.TileSet.unionEqUniv_reindex_iff_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:57:14.498733+00:00
-- url     : https://prove2.me/submissions/5aefa543-70bd-4aa9-b9c5-cc206c5b465d

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' : Type*}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (h : Surjective e) : (t.reindex e).UnionEqUniv ↔ t.UnionEqUniv :=
  unionEq_reindex_iff_of_surjective h
end DiscreteTiling.TileSet
