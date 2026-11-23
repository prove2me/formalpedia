-- Prove2me | solution 1 for DiscreteTiling.TileSet.isTilingOf_smul_set_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:22:33.291076+00:00
-- url     : https://prove2.me/submissions/bda4b10b-53a8-4043-849d-02c7e0401f5b

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
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
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    t.IsTilingOf (g • s) ↔ (g⁻¹ • t).IsTilingOf s := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_cancel g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _
end DiscreteTiling.TileSet
