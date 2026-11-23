-- Prove2me | solution 1 for DiscreteTiling.TileSet.mem_smul_symmetryGroup_iff_smul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:09:35.346118+00:00
-- url     : https://prove2.me/submissions/b578b74b-ac63-4532-b7c2-86968db65e72

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_mem_smul_symmetryGroup_iff
public import Theorems.Thm_DiscreteTiling_TileSet_mem_smul_iff_smul_inv_mem


set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    x ∈ ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔
      g⁻¹ • x ∈ (pt : PlacedTile ps) := by
  simp_rw [mem_smul_symmetryGroup_iff, Subgroup.smul_def, Subgroup.coe_inv,
           PlacedTile.mem_smul_iff_smul_inv_mem]
end DiscreteTiling.TileSet
