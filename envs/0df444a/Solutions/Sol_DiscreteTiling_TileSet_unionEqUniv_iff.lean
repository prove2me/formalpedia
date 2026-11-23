-- Prove2me | solution 1 for DiscreteTiling.TileSet.unionEqUniv_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:09:04.252547+00:00
-- url     : https://prove2.me/submissions/4d1570c6-9862-4cd9-ab1a-7d45651fac2d

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
theorem _root_.solution {t : TileSet ps ιₜ} : t.UnionEqUniv ↔ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl
end DiscreteTiling.TileSet
