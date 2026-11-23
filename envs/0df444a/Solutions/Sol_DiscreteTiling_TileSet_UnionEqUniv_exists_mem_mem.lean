-- Prove2me | solution 1 for DiscreteTiling.TileSet.UnionEqUniv.exists_mem_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:09:31.713946+00:00
-- url     : https://prove2.me/submissions/b51fec82-6260-4432-ab69-092bbc1c454e

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Theorems.Thm_DiscreteTiling_TileSet_UnionEq_exists_mem_mem_iff
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
    ∃ pt ∈ t, x ∈ pt := by
  rw [unionEqUniv_iff_unionEq] at h
  rw [UnionEq.exists_mem_mem_iff h]
  exact Set.mem_univ _
end UnionEqUniv
end DiscreteTiling.TileSet
