-- Prove2me | solution 1 for DiscreteTiling.TileSet.weaklyPeriodic_iff_of_relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:17:34.108366+00:00
-- url     : https://prove2.me/submissions/996945e2-42f2-4f53-81d2-a1e2970c6069

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
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
theorem _root_.solution {n : ℕ} {t : TileSet ps ιₜ} {H : Subgroup G}
    (hi : H.relIndex t.symmetryGroup ≠ 0) :
    t.WeaklyPeriodic n ↔
      ∃ f : (Fin n → Multiplicative ℤ) →* (H ⊓ t.symmetryGroup : Subgroup G), Injective f := by
  refine ⟨fun ⟨f, hf⟩ ↦ ?_,
    fun ⟨f, hf⟩ ↦ ⟨(Subgroup.inclusion inf_le_right).comp f, fun x y hxy ↦ hf (by simpa using hxy)⟩⟩
  let f' : (Fin n → Multiplicative ℤ) →* (Fin n → Multiplicative ℤ) :=
    powMonoidHom (H.relIndex t.symmetryGroup)!
  have hf' : Injective f' := by
    intro x₁ x₂ he
    simp only [powMonoidHom_apply, f'] at he
    ext i
    suffices (x₁ i) ^ (H.relIndex t.symmetryGroup)! = (x₂ i) ^ (H.relIndex t.symmetryGroup)! by
      rwa [← zpow_natCast, ← zpow_natCast, zpow_left_inj (mod_cast (Nat.factorial_ne_zero _))]
        at this
    simp_rw [← Pi.pow_apply, he]
  have h : ∀ x : Fin n → Multiplicative ℤ,
      (((Subgroup.subtype _).comp f).comp f') x ∈ H ⊓ t.symmetryGroup := by
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, comp_apply, f', powMonoidHom_apply,
      map_pow, SubmonoidClass.coe_pow]
    exact fun x ↦ Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd hi (SetLike.coe_mem _)
      (fun _ ↦ Nat.dvd_factorial)
  refine ⟨(((Subgroup.subtype _).comp f).comp f').codRestrict _ h, ?_⟩
  simp only [MonoidHom.injective_codRestrict, MonoidHom.coe_comp, Subgroup.coe_subtype]
  exact (Subtype.val_injective.comp hf).comp hf'
end DiscreteTiling.TileSet
