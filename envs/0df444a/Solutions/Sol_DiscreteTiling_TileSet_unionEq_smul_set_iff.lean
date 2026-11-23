-- Prove2me | solution 1 for DiscreteTiling.TileSet.unionEq_smul_set_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:22:02.40238+00:00
-- url     : https://prove2.me/submissions/ceb10b22-d682-4761-aca8-361ab84f394c

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Theorems.Thm_DiscreteTiling_TileSetFunction_smul_iff
public import Theorems.Thm_DiscreteTiling_VarTileSetFunction_smul_iff


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
theorem _root_.solution {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    t.UnionEq (g • s) ↔ (g⁻¹ • t).UnionEq s := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_cancel g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _
end DiscreteTiling.TileSet
