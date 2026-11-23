-- Prove2me | solution 1 for DiscreteTiling.TileSet.weaklyPeriodic_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:23:25.059773+00:00
-- url     : https://prove2.me/submissions/04d998b3-f132-4697-b9a1-b1bf277429a0

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_weaklyPeriodic_iff
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
public import Theorems.Thm_DiscreteTiling_TileSet_isTilingOf_empty
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_quotientPlacedTileOfquotientTilePoint_apply_mk
public import Theorems.Thm_DiscreteTiling_TileSet_quotientPointOfquotientTilePoint_apply_mk
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
attribute [local simp] DiscreteTiling.TileSet.isTilingOf_empty
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.quotientPlacedTileOfquotientTilePoint_apply_mk
attribute [local simp] DiscreteTiling.TileSet.quotientPointOfquotientTilePoint_apply_mk
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.unionEqUniv_reindex_iff_of_surjective
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_apply
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_const
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction



set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Nat Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} :
    t.WeaklyPeriodic 1 ↔ ∃ g ∈ t.symmetryGroup, ¬IsOfFinOrder g := by
  rw [weaklyPeriodic_iff]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨g, hg, ho⟩ ↦ ?_⟩
  · refine ⟨f (fun _ ↦ Multiplicative.ofAdd 1), (f (fun _ ↦ Multiplicative.ofAdd 1)).property, ?_⟩
    rw [← injective_zpow_iff_not_isOfFinOrder]
    intro a₁ a₂ h
    dsimp only at h
    simp_rw [← SubgroupClass.coe_zpow, ← map_zpow, ← Subtype.ext_iff, hf.eq_iff, funext_iff,
      Pi.pow_apply, forall_const, ← ofAdd_zsmul] at h
    simpa using h
  · refine ⟨(zpowersHom (t.symmetryGroup) ⟨g, hg⟩).comp (Pi.evalMonoidHom _ 0), ?_⟩
    rw [← injective_zpow_iff_not_isOfFinOrder] at ho
    simp only [Injective, MonoidHom.coe_comp, comp_apply, Pi.evalMonoidHom_apply,
      zpowersHom_apply, Subtype.ext_iff, SubgroupClass.coe_zpow]
    intro a₁ a₂ h
    have h' := ho h
    simpa [funext_iff_of_subsingleton] using h'
end DiscreteTiling.TileSet
