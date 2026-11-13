-- Prove2me | solution 1 for CrossedProductGroups.Classification.corollary_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:56:21.377856+00:00
-- url     : https://prove2.me/submissions/e841430c-9773-40aa-a139-aa660ace3b8a

import Definitions.Def_CrossedProductGroups_Classification_E2
import Theorems.Thm_CrossedProductGroups_Classification_proposition_3_4
import Mathlib.Tactic.Group
import Mathlib.CategoryTheory.Iso
open CategoryTheory
set_option autoImplicit false

open CrossedProductGroups.Classification


theorem solution {H G : Type*} [Group H] [Group G] (c c' : E2 H G) (m : c ⟶ c') :
    CategoryTheory.IsIso m ↔
      ∃ (η : H ≃* H) (γ : G ≃* G),
        η.toMonoidHom = (m : E2Hom c c').η ∧ γ.toMonoidHom = (m : E2Hom c c').γ ∧
        ∃! t : G → H,
          (∀ g : G, ∀ h : H,
            c'.1.1 g h = η (t g * c.1.1 (γ.symm g) (η.symm h) * (t g)⁻¹)) ∧
          (∀ g₁ g₂ : G, c'.1.2 g₁ g₂ =
            η (t g₁ * c.1.1 (γ.symm g₁) (t g₂) * c.1.2 (γ.symm g₁) (γ.symm g₂) *
              (t (g₁ * g₂))⁻¹)) ∧
          ∀ h : H, ∀ g : G, (m : E2Hom c c').ψ (h, g) = (η (h * (t (γ g))⁻¹), γ g) := by
  classical
  constructor
  · intro hm
    letI : IsIso m := hm
    let mi : E2Hom c' c := CategoryTheory.inv m
    have h1 : E2Hom.comp m mi = E2Hom.id c := CategoryTheory.IsIso.hom_inv_id m
    have h2 : E2Hom.comp mi m = E2Hom.id c' := CategoryTheory.IsIso.inv_hom_id m
    let η : H ≃* H := MonoidHom.toMulEquiv m.η mi.η
      (congrArg E2Hom.η h1) (congrArg E2Hom.η h2)
    let γ : G ≃* G := MonoidHom.toMulEquiv m.γ mi.γ
      (congrArg E2Hom.γ h1) (congrArg E2Hom.γ h2)
    obtain ⟨r,⟨hC,hF,hψ⟩,_⟩ := (proposition_3_4 c c' m.η m.γ m.ψ).mp ⟨m,rfl,rfl,rfl⟩
    change (∀ g h, η (c.1.1 g h) * r g = r g * c'.1.1 (γ g) (η h)) at hC
    change (∀ g k, r g * c'.1.1 (γ g) (r k) * c'.1.2 (γ g) (γ k) =
      η (c.1.2 g k) * r (g*k)) at hF
    change (∀ h g, m.ψ (h,g) = (η h*r g,γ g)) at hψ
    let t : G → H := fun g => (η.symm (r (γ.symm g)))⁻¹
    refine ⟨η,γ,rfl,rfl,t,⟨?_,?_,?_⟩,?_⟩
    · intro g h
      obtain ⟨a,rfl⟩ := γ.surjective g
      obtain ⟨b,rfl⟩ := η.surjective h
      simp only [t,MulEquiv.symm_apply_apply,map_mul,map_inv,MulEquiv.apply_symm_apply]
      have he : c'.1.1 (γ a) (η b) = (r a)⁻¹ * (η (c.1.1 a b) * r a) := by
        rw [hC]
        group
      rw [he]
      group
    · intro g k
      obtain ⟨a,rfl⟩ := γ.surjective g
      obtain ⟨b,rfl⟩ := γ.surjective k
      rw [← γ.map_mul]
      simp only [t,MulEquiv.symm_apply_apply]
      have he : η (c.1.1 a (η.symm (r b))) =
          r a * c'.1.1 (γ a) (r b) * (r a)⁻¹ := by
        have hh := hC a (η.symm (r b))
        rw [MulEquiv.apply_symm_apply] at hh
        exact eq_mul_inv_of_mul_eq hh
      have hf : η (c.1.2 a b) =
          r a * c'.1.1 (γ a) (r b) * c'.1.2 (γ a) (γ b) * (r (a*b))⁻¹ :=
        eq_mul_inv_of_mul_eq (hF a b).symm
      simp only [map_mul,map_inv,MulEquiv.apply_symm_apply,he,hf]
      group
    · intro h g
      rw [hψ]
      simp [t,map_mul]
    · intro t' ht'
      funext x
      have hh := congrArg Prod.fst (ht'.2.2 1 (γ.symm x))
      rw [hψ] at hh
      change η 1 * r (γ.symm x) = η (1 * (t' (γ (γ.symm x)))⁻¹) at hh
      simp only [map_one,one_mul,MulEquiv.apply_symm_apply] at hh
      apply inv_injective
      apply η.injective
      simpa only [t,inv_inv,MulEquiv.apply_symm_apply] using hh.symm
  · rintro ⟨η,γ,hη,hγ,t,⟨hC,hF,hψ⟩,_⟩
    let ep : H × G ≃ H × G :=
      { toFun := m.ψ
        invFun := fun y => (η.symm y.1 * t y.2,γ.symm y.2)
        left_inv := by
          rintro ⟨h,g⟩
          rw [hψ]
          simp
        right_inv := by
          rintro ⟨h,g⟩
          rw [hψ]
          simp }
    let mi : E2Hom c' c :=
      { η := η.symm.toMonoidHom
        γ := γ.symm.toMonoidHom
        ψ := ep.symm
        map_mul := by
          intro x y
          apply ep.injective
          change m.ψ (ep.symm (crossedMul c'.1.1 c'.1.2 x y)) =
            m.ψ (crossedMul c.1.1 c.1.2 (ep.symm x) (ep.symm y))
          rw [m.map_mul]
          exact (ep.apply_symm_apply _).trans (congrArg₂ (crossedMul c'.1.1 c'.1.2)
            (ep.apply_symm_apply x).symm (ep.apply_symm_apply y).symm)
        comm_inl := by
          intro h
          apply ep.injective
          change ep (ep.symm (h,1)) = m.ψ (η.symm h,1)
          rw [ep.apply_symm_apply,m.comm_inl,← hη]
          simp
        comm_snd := by
          intro x
          apply γ.injective
          have hh := m.comm_snd (ep.symm x)
          change (ep (ep.symm x)).2 = m.γ (ep.symm x).2 at hh
          rw [ep.apply_symm_apply,← hγ] at hh
          exact hh.symm.trans (γ.apply_symm_apply x.2).symm }
    let e : c ≅ c' :=
      { hom := m
        inv := mi
        hom_inv_id := by
          apply E2Hom.ext
          · ext x
            change η.symm (m.η x) = x
            rw [← hη]
            exact η.symm_apply_apply x
          · ext x
            change γ.symm (m.γ x) = x
            rw [← hγ]
            exact γ.symm_apply_apply x
          · funext x
            exact ep.symm_apply_apply x
        inv_hom_id := by
          apply E2Hom.ext
          · ext x
            change m.η (η.symm x) = x
            rw [← hη]
            exact η.apply_symm_apply x
          · ext x
            change m.γ (γ.symm x) = x
            rw [← hγ]
            exact γ.apply_symm_apply x
          · funext x
            exact ep.apply_symm_apply x }
    exact e.isIso_hom
