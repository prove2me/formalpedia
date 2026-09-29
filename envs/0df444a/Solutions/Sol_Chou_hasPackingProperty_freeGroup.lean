-- Prove2me | solution 1 for Chou.hasPackingProperty_freeGroup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-19T17:56:20.141513+00:00
-- url     : https://prove2.me/submissions/e21d3b6c-fd7b-482a-9289-2766d3399d9f

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Theorems.Thm_Chou_residuallyFinite_freeGroup
import Theorems.Thm_Chou_hasPackingProperty_of_forall_finite_exists_quotient
import Theorems.Thm_Chou_hasPackingProperty_of_finite
import Mathlib

namespace Chou
namespace Lib

open Chou

/-- Chou p. 406: "each free group has property (P) since it is residually finite."

Given a finite `F`, for each of the finitely many differences `x⁻¹ * y` with `x, y ∈ F`
residual finiteness supplies a finite-index normal subgroup omitting it; the intersection `K`
of these is again normal of finite index, so `G ⧸ K` is finite and has property (P), and
`F` embeds in `G ⧸ K`.  Lemma 4.6(a) then gives property (P) for `G`. -/
theorem hasPackingProperty_freeGroup' (α : Type*) : HasPackingProperty (FreeGroup α) := by
  classical
  have : Group.ResiduallyFinite (FreeGroup α) := residuallyFinite_freeGroup α
  apply hasPackingProperty_of_forall_finite_exists_quotient
  intro F hF
  -- For every `g` pick a finite-index normal subgroup omitting `g` when `g ≠ 1`.
  have hchoice : ∀ g : FreeGroup α,
      ∃ H : FiniteIndexNormalSubgroup (FreeGroup α), g ≠ 1 → g ∉ H := by
    intro g
    by_cases hg : g = 1
    · exact ⟨FiniteIndexNormalSubgroup.ofSubgroup (⊤ : Subgroup (FreeGroup α)),
        fun h => absurd hg h⟩
    · obtain ⟨H, hH⟩ := Group.exists_finiteIndexNormalSubgroup_notMem g hg
      exact ⟨H, fun _ => hH⟩
  choose f hf using hchoice
  -- The finite set of differences coming from `F`.
  set T : Finset (FreeGroup α) :=
    (hF.toFinset ×ˢ hF.toFinset).image (fun p => p.1⁻¹ * p.2) with hT
  set K : Subgroup (FreeGroup α) := ⨅ t : {x // x ∈ T}, (f (t : FreeGroup α)).toSubgroup with hK
  have hKnormal : K.Normal :=
    Subgroup.normal_iInf_normal fun t => (f (t : FreeGroup α)).isNormal'
  have hKindex : K.FiniteIndex :=
    Subgroup.finiteIndex_iInf fun t => (f (t : FreeGroup α)).isFiniteIndex'
  have : Finite (FreeGroup α ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨K, hKnormal, hasPackingProperty_of_finite, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have hmem : x⁻¹ * y ∈ T := by
    rw [hT]
    exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2
      ⟨hF.mem_toFinset.2 hx, hF.mem_toFinset.2 hy⟩, rfl⟩
  have h1 : x⁻¹ * y ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  have hin : x⁻¹ * y ∈ K := QuotientGroup.eq.mp hxy
  have hle : K ≤ (f (x⁻¹ * y)).toSubgroup := by
    rw [hK]
    exact iInf_le (fun t : {x // x ∈ T} => (f (t : FreeGroup α)).toSubgroup) ⟨x⁻¹ * y, hmem⟩
  exact hf (x⁻¹ * y) h1 (hle hin)

end Lib
end Chou

open Chou

theorem solution (α : Type*) : HasPackingProperty (FreeGroup α) :=
  Chou.Lib.hasPackingProperty_freeGroup' α
