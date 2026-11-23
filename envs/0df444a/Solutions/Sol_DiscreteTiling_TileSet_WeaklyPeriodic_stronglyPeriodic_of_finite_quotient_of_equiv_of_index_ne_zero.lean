-- Prove2me | solution 1 for DiscreteTiling.TileSet.WeaklyPeriodic.stronglyPeriodic_of_finite_quotient_of_equiv_of_index_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:19:18.306637+00:00
-- url     : https://prove2.me/submissions/4d2a5bd6-5d7e-4712-bb55-affe0dcdcbce

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_of_finite_quotient_of_index_ne_zero
public import Theorems.Thm_DiscreteTiling_TileSet_weaklyPeriodic_iff_of_index_ne_zero

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
namespace WeaklyPeriodic
theorem _root_.solution {n : ℕ}
    {t : TileSet ps ιₜ} (h : t.WeaklyPeriodic n) [Finite <| MulAction.orbitRel.Quotient G X]
    {H : Subgroup G} (e : H ≃* (Fin n → Multiplicative ℤ)) (hi : H.index ≠ 0) :
    t.StronglyPeriodic := by
  refine stronglyPeriodic_of_finite_quotient_of_index_ne_zero ?_
  rw [weaklyPeriodic_iff_of_index_ne_zero hi] at h
  rcases h with ⟨f, hf⟩
  rw [← Subgroup.relIndex_top_right] at hi ⊢
  refine Subgroup.relIndex_ne_zero_trans ?_ hi
  rw [← Subgroup.inf_relIndex_left]
  suffices (f.range.map (Subgroup.subtype _)).relIndex H ≠ 0 from
    mt (Subgroup.relIndex_eq_zero_of_le_left (Subgroup.map_subtype_le f.range)) this
  let f' : f.range ≃* (Fin n → Multiplicative ℤ) :=
    ((MulEquiv.subgroupCongr f.range_eq_map).trans (Subgroup.equivMapOfInjective _ _ hf).symm).trans
    Subgroup.topEquiv
  let e' : (Fin n → Multiplicative ℤ) →* H := ↑e.symm
  have he' : Surjective e' := e.symm.surjective
  rw [Subgroup.relIndex, ← Subgroup.index_comap_of_surjective _ he',
      Int.subgroup_index_ne_zero_iff]
  exact ⟨((((MulEquiv.subgroupCongr
    (((Subgroup.map (H ⊓ t.symmetryGroup).subtype f.range).subgroupOf H).map_equiv_eq_comap_symm
      e).symm).trans (Subgroup.equivMapOfInjective _ _ e.injective).symm).trans
    (Subgroup.subgroupOfEquivOfLe ((Subgroup.map_subtype_le _).trans inf_le_left))).trans
    (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm).trans f'⟩
end WeaklyPeriodic
end DiscreteTiling.TileSet
