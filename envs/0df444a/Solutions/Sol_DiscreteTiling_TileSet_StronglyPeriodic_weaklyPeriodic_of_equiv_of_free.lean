-- Prove2me | solution 1 for DiscreteTiling.TileSet.StronglyPeriodic.weaklyPeriodic_of_equiv_of_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:23:40.837793+00:00
-- url     : https://prove2.me/submissions/0fa0c3ae-4363-4307-899f-a9983a4ec785

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_StronglyPeriodic_index_ne_zero_of_free

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
theorem _root_.solution [Nonempty X] {n : ℕ} {t : TileSet ps ιₜ}
    (h : t.StronglyPeriodic) {H : Subgroup G} (e : H ≃* (Fin n → Multiplicative ℤ))
    [IsCancelSMul H X] (hi : H.index ≠ 0) : t.WeaklyPeriodic n := by
  let e' : (Fin n → Multiplicative ℤ) →* H := ↑e.symm
  have he' : Surjective e' := e.symm.surjective
  have hsi := Subgroup.index_inf_ne_zero (StronglyPeriodic.index_ne_zero_of_free h hi) hi
  rw [← Subgroup.relIndex_top_right, ← Subgroup.relIndex_inf_mul_relIndex, mul_ne_zero_iff,
      Subgroup.relIndex_top_right, and_iff_left hi, inf_top_eq, Subgroup.relIndex,
      ← Subgroup.index_comap_of_surjective _ he', Int.subgroup_index_ne_zero_iff] at hsi
  rcases hsi with ⟨f⟩
  let f₁ : (Fin n → Multiplicative ℤ) ≃* (t.symmetryGroup ⊓ H : Subgroup G) :=
    (((f.symm.trans
    (MulEquiv.subgroupCongr (Subgroup.map_equiv_eq_comap_symm _ _).symm)).trans
    (Subgroup.equivMapOfInjective _ _ e.injective).symm).trans
    (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right _ _).symm)).trans
    (Subgroup.subgroupOfEquivOfLe inf_le_right)
  let f₂ : (Fin n → Multiplicative ℤ) →* (t.symmetryGroup ⊓ H : Subgroup G) := ↑f₁
  have hf₂ : Injective f₂ := f₁.injective
  let f₃ : (t.symmetryGroup ⊓ H : Subgroup G) →* t.symmetryGroup := Subgroup.inclusion inf_le_left
  have hf₃ : Injective f₃ := Subgroup.inclusion_injective _
  exact ⟨f₃.comp f₂, hf₃.comp hf₂⟩
end StronglyPeriodic
end DiscreteTiling.TileSet
