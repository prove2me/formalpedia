-- Prove2me | solution 1 for DiscreteTiling.TileSet.unionEqUniv_iff_unionEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:58:36.350811+00:00
-- url     : https://prove2.me/submissions/0a0357cb-26b7-4229-8cb3-229530322a2b

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
theorem _root_.solution {t : TileSet ps ιₜ} : t.UnionEqUniv ↔ t.UnionEq Set.univ :=
  Iff.rfl
end DiscreteTiling.TileSet
