-- Prove2me | solution 1 for Chou.hasPackingProperty_of_residuallyElementaryAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T18:53:14.188987+00:00
-- url     : https://prove2.me/submissions/4149e2a1-d4dd-4db5-8186-6b60e8ea2ebf

import Theorems.Thm_Chou_hasPackingProperty_of_elementaryAmenable
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib
import Theorems.Thm_Chou_hasPackingProperty_of_forall_finite_exists_quotient

/-! # Chou §2: Propositions 2.1 and 2.2

`Constructible` is closed under subgroups and quotients (one structural induction proving both at
once — Chou's transfinite induction), hence coincides with `ElementaryAmenable`. -/

universe u

namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-- The image of `B` in `G ⧸ M` is the quotient of `B` by `M ∩ B`. -/
noncomputable def quotientSubgroupOfEquivMap {G : Type*} [Group G] (B M : Subgroup G) [M.Normal] :
    B ⧸ M.subgroupOf B ≃* ↥(B.map (mk' M)) :=
  have h1 : M.subgroupOf B = ((mk' M).comp B.subtype).ker := by
    rw [← MonoidHom.comap_ker, ker_mk', comap_subtype]
  have h2 : ((mk' M).comp B.subtype).range = B.map (mk' M) := by
    rw [MonoidHom.range_comp, range_subtype]
  (quotientMulEquivOfEq h1).trans
    ((quotientKerEquivRange ((mk' M).comp B.subtype)).trans (MulEquiv.subgroupCongr h2))

end Lib
end Chou

/-! # Chou §2: Theorem 2.3 and Corollary 2.4 -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Small tools -/

/-! ### Locally finite groups -/

/-! ### Periodic groups lie in NF; NF ∖ EG is nonempty -/

/-! ### Corollary 2.4 -/

end Lib
end Chou

/-! # Chou §4: packings and property (P) — the basic cases and Lemmas 4.1, 4.6 (a) -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Packings -/

/-! ### Finite groups and the integers -/



/-! ### Lemma 4.1 (a): directed unions -/


end Lib
end Chou

/-! # Chou §4: Lemma 4.1 (b) (extensions) and Lemma 4.6 (a) -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Lemma 4.1 (b) -/


/-! ### Lemma 4.6 (a) -/


end Lib
end Chou

/-! # Chou §4: finitely generated abelian groups, Proposition 4.2, Corollary 4.7 -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Products -/

/-! ### Abelian groups -/

/-! ### Proposition 4.2 -/

/-! ### Corollary 4.7 -/

/-- The quotient by an intersection of two normal subgroups with elementary amenable quotients
is elementary amenable. -/
theorem elementaryAmenable_quotient_inf {G : Type u} [Group G] (K₁ K₂ : Subgroup G) [K₁.Normal]
    [K₂.Normal] (h₁ : ElementaryAmenable (G ⧸ K₁)) (h₂ : ElementaryAmenable (G ⧸ K₂)) :
    ElementaryAmenable (G ⧸ (K₁ ⊓ K₂)) := by
  haveI : (K₁.map (mk' (K₁ ⊓ K₂))).Normal := ‹K₁.Normal›.map _ (mk'_surjective _)
  refine ElementaryAmenable.extension (K₁.map (mk' (K₁ ⊓ K₂))) ?_ ?_
  · -- `K₁ / (K₁ ⊓ K₂) ≅ image of K₁ in G ⧸ K₂`
    have e₁ : ↥(K₁.map (mk' (K₁ ⊓ K₂))) ≃* K₁ ⧸ (K₁ ⊓ K₂).subgroupOf K₁ :=
      (quotientSubgroupOfEquivMap K₁ (K₁ ⊓ K₂)).symm
    have hEq : (K₁ ⊓ K₂).subgroupOf K₁ = K₂.subgroupOf K₁ := by
      ext x; simp [mem_subgroupOf, x.2]
    have e₂ : K₁ ⧸ (K₁ ⊓ K₂).subgroupOf K₁ ≃* ↥(K₁.map (mk' K₂)) :=
      (quotientMulEquivOfEq hEq).trans (quotientSubgroupOfEquivMap K₁ K₂)
    exact ElementaryAmenable.of_mulEquiv (e₁.trans e₂).symm (ElementaryAmenable.subgroup _ h₂)
  · have e : (G ⧸ (K₁ ⊓ K₂)) ⧸ K₁.map (mk' (K₁ ⊓ K₂)) ≃* G ⧸ K₁ :=
      quotientQuotientEquivQuotient (K₁ ⊓ K₂) K₁ inf_le_left
    exact ElementaryAmenable.of_mulEquiv e.symm h₁

theorem hasPackingProperty_of_residuallyElementaryAmenable' {G : Type u} [Group G]
    (h : ResiduallyElementaryAmenable G) : HasPackingProperty G := by
  classical
  apply Chou.hasPackingProperty_of_forall_finite_exists_quotient
  intro F hF
  -- for a finite set of pairs, a common separating quotient
  have key : ∀ P : Finset (G × G), ∃ (K : Subgroup G) (_ : K.Normal),
      ElementaryAmenable (G ⧸ K) ∧ ∀ q ∈ P, q.1 ≠ q.2 → q.1⁻¹ * q.2 ∉ K := by
    intro P
    induction P using Finset.induction_on with
    | empty =>
      refine ⟨⊤, inferInstance, ?_, by simp⟩
      haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
      exact ElementaryAmenable.of_finite _
    | insert q P _ ih =>
      obtain ⟨K, hKn, hK, hsep⟩ := ih
      by_cases hq : q.1 = q.2
      · exact ⟨K, hKn, hK, fun r hr hne => hsep r (by
          rcases Finset.mem_insert.mp hr with rfl | hr
          · exact absurd hq hne
          · exact hr) hne⟩
      · obtain ⟨K', hK'n, hx, hK'⟩ := h (q.1⁻¹ * q.2) (by
          intro h0; exact hq (inv_mul_eq_one.mp h0))
        refine ⟨K ⊓ K', inferInstance, elementaryAmenable_quotient_inf K K' hK hK', ?_⟩
        intro r hr hne
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact fun hm => hx hm.2
        · exact fun hm => hsep r hr hne hm.1
  obtain ⟨K, hKn, hK, hsep⟩ := key (hF.toFinset ×ˢ hF.toFinset)
  refine ⟨K, hKn, Chou.hasPackingProperty_of_elementaryAmenable hK, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  exact hsep (x, y) (Finset.mem_product.mpr ⟨hF.mem_toFinset.mpr hx, hF.mem_toFinset.mpr hy⟩) hne
    ((QuotientGroup.eq).mp hxy)

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G]
    (h : ResiduallyElementaryAmenable G) : HasPackingProperty G :=
  Chou.Lib.hasPackingProperty_of_residuallyElementaryAmenable' h
