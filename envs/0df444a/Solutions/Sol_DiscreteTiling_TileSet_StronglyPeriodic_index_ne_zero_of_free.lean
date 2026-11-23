-- Prove2me | solution 1 for DiscreteTiling.TileSet.StronglyPeriodic.index_ne_zero_of_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:11:03.996853+00:00
-- url     : https://prove2.me/submissions/5eecec9c-5787-492b-a4a7-df32922fc512

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_iff
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
namespace StronglyPeriodic
theorem _root_.solution [Nonempty X] {t : TileSet ps ιₜ}
    (h : t.StronglyPeriodic) {H : Subgroup G} [IsCancelSMul H X] (hi : H.index ≠ 0) :
    t.symmetryGroup.index ≠ 0 := by
  rw [stronglyPeriodic_iff] at h
  have hr : H.relIndex t.symmetryGroup ≠ 0 := mt Subgroup.index_eq_zero_of_relIndex_eq_zero hi
  suffices t.symmetryGroup.relIndex H ≠ 0 by
    rw [← Subgroup.relIndex_top_right] at hi ⊢
    exact Subgroup.relIndex_ne_zero_trans this hi
  rw [Subgroup.relIndex] at hr ⊢
  have hf := Subgroup.finite_quotient_of_finite_quotient_of_index_ne_zero hr (X := X)
  rw [MulAction.orbitRel.Quotient, MulAction.orbitRel_subgroupOf, inf_comm,
    ← MulAction.orbitRel_subgroupOf, ← MulAction.orbitRel.Quotient,
    (MulAction.equivSubgroupOrbits X _).finite_iff] at hf
  intro h0
  rw [Subgroup.index_eq_zero_iff_infinite] at h0
  revert hf
  rw [imp_false, not_finite_iff_infinite]
  have hne : Nonempty (MulAction.orbitRel.Quotient H X) := by simpa [nonempty_quotient_iff]
  have x := Classical.arbitrary (MulAction.orbitRel.Quotient H X)
  convert Infinite.sigma_of_right (a := x)
  have y : MulAction.orbitRel.Quotient.orbit x :=
    (MulAction.orbitRel.Quotient.nonempty_orbit x).to_subtype.some
  have : IsCancelSMul H x.orbit := by
    rw [isCancelSMul_iff_stabilizer_eq_bot]
    intro z
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
    refine ⟨fun hs ↦ ?_, fun hs ↦ by simp [hs]⟩
    suffices g ∈ MulAction.stabilizer H (z : X) by
      simpa using this
    rw [MulAction.mem_stabilizer_iff, ← MulAction.orbitRel.Quotient.orbit.coe_smul, hs]
  rw [(MulAction.equivSubgroupOrbitsQuotientGroup y _).infinite_iff]
  exact h0
end StronglyPeriodic
end DiscreteTiling.TileSet
