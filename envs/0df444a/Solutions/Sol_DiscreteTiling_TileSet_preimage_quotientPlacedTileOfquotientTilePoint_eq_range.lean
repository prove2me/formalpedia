-- Prove2me | solution 1 for DiscreteTiling.TileSet.preimage_quotientPlacedTileOfquotientTilePoint_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:10:32.544706+00:00
-- url     : https://prove2.me/submissions/572cad8c-88d2-474d-bafd-8d816b5ff0e0

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_mem_smul_symmetryGroup_iff_smul_inv_mem
public import Theorems.Thm_DiscreteTiling_TileSet_coe_smul_tilePoint
public import Theorems.Thm_DiscreteTiling_TileSet_quotientPlacedTileOfquotientTilePoint_apply_mk
public import Theorems.Thm_DiscreteTiling_TileSet_quotientPointOfquotientTilePoint_apply_mk
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_apply
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_const
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_toTileSetFunction
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_empty
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_of_subsingleton
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_univ_iff
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
public import Theorems.Thm_DiscreteTiling_TileSet_unionEqUniv_reindex_iff_of_surjective
attribute [local simp] DiscreteTiling.TileSet.coeSet_sigma
attribute [local simp] DiscreteTiling.TileSet.coeSet_sum
attribute [local simp] DiscreteTiling.TileSet.coe_sigma
attribute [local simp] DiscreteTiling.TileSet.coe_sum
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_empty
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_of_subsingleton
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_univ_iff
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.unionEqUniv_reindex_iff_of_surjective
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_apply
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_const
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction


attribute [local simp] DiscreteTiling.TileSet.quotientPlacedTileOfquotientTilePoint_apply_mk
attribute [local simp] DiscreteTiling.TileSet.quotientPointOfquotientTilePoint_apply_mk

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
theorem _root_.solution {t : TileSet ps ιₜ}
    (pt : (t : Set (PlacedTile ps))) : t.quotientPlacedTileOfquotientTilePoint ⁻¹' {⟦pt⟧} =
      Set.range (fun x : {x // x ∈ (pt : PlacedTile ps)} ↦ ⟦⟨(pt, x), x.property⟩⟧) := by
  refine Set.Subset.antisymm (fun x h ↦ ?_) (Set.range_subset_iff.2 fun x ↦ (Set.mem_singleton _))
  rw [Set.mem_preimage] at h
  induction x using Quotient.inductionOn' with
  | h pt' =>
    rcases pt' with ⟨⟨pt', x⟩, hx⟩
    simp only [quotientPlacedTileOfquotientTilePoint_apply_mk, Set.mem_singleton_iff] at h
    rw [← @Quotient.mk''_eq_mk, Quotient.eq''] at h
    rcases h with ⟨g, rfl⟩
    dsimp only at hx
    rw [mem_smul_symmetryGroup_iff_smul_inv_mem] at hx
    refine ⟨⟨g⁻¹ • x, hx⟩, ?_⟩
    simp only
    rw [← @Quotient.mk''_eq_mk, Quotient.eq'', MulAction.orbitRel_apply]
    refine ⟨g⁻¹, Subtype.ext_iff.2 ?_⟩
    simp [coe_smul_tilePoint]
end DiscreteTiling.TileSet
