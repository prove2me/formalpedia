-- Prove2me | solution 1 for DiscreteTiling.TileSet.UnionEqUniv.exists_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:22:11.329154+00:00
-- url     : https://prove2.me/submissions/7da71a89-d72f-4757-aad9-c6ce4a4eedd1

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Theorems.Thm_DiscreteTiling_TileSet_unionEqUniv_iff_unionEq

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
namespace UnionEqUniv
theorem _root_.solution {t : TileSet ps ιₜ} (h : t.UnionEqUniv) (x : X) :
    ∃ i, x ∈ t i := by
  rw [unionEqUniv_iff_unionEq] at h
  rw [UnionEq.exists_mem_iff h]
  exact Set.mem_univ _
end UnionEqUniv
end DiscreteTiling.TileSet
