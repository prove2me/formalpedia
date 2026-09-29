-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_ker_le_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4d5b8c32-3ef7-5894-803e-65b9d074105e

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_ker_le_span
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace H1Aux

open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem specMap_ofHom_id (S : Type) [CommRing S] :
    Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 (Spec (CommRingCat.of S)) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]

theorem specMap_ofHom_comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'') :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (e : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) (P' Q' : SchemeHomOver t₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t₁ P Q).1 = (L.mul t₂ P' Q').1 := by
  subst e
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

theorem exists_factor {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₁ S₂ : Type} [CommRing S] [CommRing S₁] [CommRing S₂] (φ : S →+* S₁) (ψ : S₁ →+* S₂)
    (E : FakeEllipticCurve Λ N S)
    (E₁ : FakeEllipticCurve Λ N S₁) (g₁ : E₁.A ⟶ E.A) (h₁ : FakeEllipticCurve.IsPullbackVia φ E E₁ g₁)
    (E₂ : FakeEllipticCurve Λ N S₂) (g₂ : E₂.A ⟶ E.A) (h₂ : FakeEllipticCurve.IsPullbackVia (ψ.comp φ) E E₂ g₂) :
    ∃ h : E₂.A ⟶ E₁.A, h ≫ g₁ = g₂ ∧ FakeEllipticCurve.IsPullbackVia ψ E₁ E₂ h := by
  obtain ⟨sq₁, hmul₁, hact₁, hlev₁⟩ := h₁
  obtain ⟨sq₂, hmul₂, hact₂, hlev₂⟩ := h₂
  have hc := specMap_ofHom_comp φ ψ
  have w₂ : g₂ ≫ E.f = (E₂.f ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [sq₂.w, hc, Category.assoc]
  let h : E₂.A ⟶ E₁.A := sq₁.lift g₂ (E₂.f ≫ Spec.map (CommRingCat.ofHom ψ)) w₂
  have hg : h ≫ g₁ = g₂ := sq₁.lift_fst _ _ _
  have hf : h ≫ E₁.f = E₂.f ≫ Spec.map (CommRingCat.ofHom ψ) := sq₁.lift_snd _ _ _
  have sqh : IsPullback h E₂.f E₁.f (Spec.map (CommRingCat.ofHom ψ)) := by
    have s : IsPullback (h ≫ g₁) E₂.f E.f (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ)) := by
      rw [hg, ← hc]; exact sq₂
    exact IsPullback.of_right s hf sq₁
  refine ⟨h, hg, sqh, ?_, ?_, ?_⟩
  · intro T t' P Q
    apply sq₁.hom_ext
    · rw [Category.assoc, hg, hmul₂ t' P Q, hmul₁]
      refine mul_val_congr E.L (by rw [hc, Category.assoc]) _ _ _ _ ?_ ?_
      · show P.1 ≫ g₂ = (P.1 ≫ h) ≫ g₁
        rw [Category.assoc, hg]
      · show Q.1 ≫ g₂ = (Q.1 ≫ h) ≫ g₁
        rw [Category.assoc, hg]
    · rw [Category.assoc, hf, ← Category.assoc, (E₂.L.mul t' P Q).2, (E₁.L.mul _ _ _).2]
  · intro x
    apply sq₁.hom_ext
    · rw [Category.assoc, hg, hact₂, Category.assoc, hact₁, ← Category.assoc, hg]
    · rw [Category.assoc, hf, ← Category.assoc, E₂.act_over, Category.assoc, E₁.act_over, hf]
  · intro T t' P hP
    have hP' := hlev₂ t' P hP
    exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
      E φ E₁ g₁ ⟨sq₁, hmul₁, hact₁, hlev₁⟩ (t' ≫ Spec.map (CommRingCat.ofHom ψ))
      ⟨P.1 ≫ h, by rw [Category.assoc, hf, ← Category.assoc, P.2]⟩
      (by obtain ⟨P₀, hP₀⟩ := hP'; exact ⟨P₀, by rw [hP₀, Category.assoc, hg]⟩)

theorem isPullbackVia_refl {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E (𝟙 E.A) := by
  have hid := specMap_ofHom_id S
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hid]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · intro T t P Q
    rw [Category.comp_id]
    exact mul_val_congr E.L (by rw [hid, Category.comp_id]) _ _ _ _ (Category.comp_id _).symm (Category.comp_id _).symm
  · intro x; simp
  · intro T t P hP
    obtain ⟨P₀, hP₀⟩ := hP
    exact ⟨P₀, by rw [Category.comp_id]; exact hP₀⟩

section Transport

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S₀ : Type} [CommRing S] [CommRing S₀] (q : S →+* S₀)

theorem liftPt_over (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀) (g : E₀.A ⟶ E.A)
    (w : g ≫ E.f = E₀.f ≫ Spec.map (CommRingCat.ofHom q))
    [IsIso (Spec.map (CommRingCat.ofHom q))] [IsIso g]
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f) :
    (P.1 ≫ inv g) ≫ E₀.f = t ≫ inv (Spec.map (CommRingCat.ofHom q)) := by
  have : inv g ≫ E₀.f = E.f ≫ inv (Spec.map (CommRingCat.ofHom q)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, w, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [Category.assoc, this, ← Category.assoc, P.2]

theorem mul_transport (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀) (g : E₀.A ⟶ E.A)
    (w : g ≫ E.f = E₀.f ≫ Spec.map (CommRingCat.ofHom q))
    (hg : FakeEllipticCurve.IsPullbackVia q E E₀ g)
    [IsIso (Spec.map (CommRingCat.ofHom q))] [IsIso g]
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f) :
    (E.L.mul t P Q).1 =
      (E₀.L.mul (t ≫ inv (Spec.map (CommRingCat.ofHom q)))
        ⟨P.1 ≫ inv g, liftPt_over q E E₀ g w P⟩ ⟨Q.1 ≫ inv g, liftPt_over q E E₀ g w Q⟩).1 ≫ g := by
  obtain ⟨sq, hmul, hact, hlev⟩ := hg
  rw [hmul]
  exact mul_val_congr E.L (by simp) _ _ _ _ (by simp) (by simp)

theorem hom_transport (E A : FakeEllipticCurve Λ N S) (E₀ A₀ : FakeEllipticCurve Λ N S₀)
    (g : E₀.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia q E E₀ g)
    (gA : A₀.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia q A A₀ gA)
    [IsIso (Spec.map (CommRingCat.ofHom q))] [IsIso g] [IsIso gA]
    (χ₀ : E₀.A ⟶ A₀.A) (hχ₀ : χ₀ ≫ A₀.f = E₀.f)
    (χ₀_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t E₀.f),
      mapPt χ₀ hχ₀ (E₀.L.mul t P Q) = A₀.L.mul t (mapPt χ₀ hχ₀ P) (mapPt χ₀ hχ₀ Q))
    (χ₀_act : ∀ x : ↥Λ, E₀.act x ≫ χ₀ = χ₀ ≫ A₀.act x) :
    ∃ (hχ : (inv g ≫ χ₀ ≫ gA) ≫ A.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
        mapPt (inv g ≫ χ₀ ≫ gA) hχ (E.L.mul t P Q) =
          A.L.mul t (mapPt (inv g ≫ χ₀ ≫ gA) hχ P) (mapPt (inv g ≫ χ₀ ≫ gA) hχ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ (inv g ≫ χ₀ ≫ gA) = (inv g ≫ χ₀ ≫ gA) ≫ A.act x) := by
  have wE : g ≫ E.f = E₀.f ≫ Spec.map (CommRingCat.ofHom q) := by
    obtain ⟨sq, -⟩ := hg; exact sq.w
  have wA : gA ≫ A.f = A₀.f ≫ Spec.map (CommRingCat.ofHom q) := by
    obtain ⟨sq, -⟩ := hgA; exact sq.w
  have hχ : (inv g ≫ χ₀ ≫ gA) ≫ A.f = E.f := by
    simp only [Category.assoc]
    rw [wA, ← Category.assoc χ₀, hχ₀, ← wE, IsIso.inv_hom_id_assoc]
  refine ⟨hχ, ?_, ?_⟩
  · intro T t P Q
    apply Subtype.ext
    simp only [mapPt_coe]
    rw [mul_transport q E E₀ g wE hg t P Q, mul_transport q A A₀ gA wA hgA t]
    have := congrArg Subtype.val (χ₀_mul (t ≫ inv (Spec.map (CommRingCat.ofHom q)))
      ⟨P.1 ≫ inv g, liftPt_over q E E₀ g wE P⟩ ⟨Q.1 ≫ inv g, liftPt_over q E E₀ g wE Q⟩)
    simp only [mapPt_coe] at this
    rw [Category.assoc, IsIso.hom_inv_id_assoc, reassoc_of% this]
    congr 1
    exact mul_val_congr A₀.L rfl _ _ _ _ (by simp [mapPt_coe]) (by simp [mapPt_coe])
  · intro x
    have hg' := hg
    have hgA' := hgA
    obtain ⟨-, -, hactE, -⟩ := hg'
    obtain ⟨-, -, hactA, -⟩ := hgA'
    have h1 : E.act x ≫ inv g = inv g ≫ E₀.act x := by
      rw [← cancel_epi g, IsIso.hom_inv_id_assoc, ← Category.assoc, ← hactE, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    simp only [Category.assoc]
    rw [← Category.assoc (E.act x), h1, Category.assoc, ← Category.assoc (E₀.act x), χ₀_act, Category.assoc, hactA]

theorem transport (hq : IsIso (Spec.map (CommRingCat.ofHom q)))
    (E A : FakeEllipticCurve Λ N S) (E₀ A₀ : FakeEllipticCurve Λ N S₀)
    (g : E₀.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia q E E₀ g)
    (gA : A₀.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia q A A₀ gA)
    (d : ℕ) (φ₀ : E₀.A ⟶ A₀.A) (φ₀' : A₀.A ⟶ E₀.A) (h₀ : FakeEllipticCurve.IsIsogenyPair d E₀ A₀ φ₀ φ₀')
    (hφ₀ : φ₀ ≫ A₀.f = E₀.f) (hl₀ : FakeEllipticCurve.PreservesLevel E₀ A₀ φ₀ hφ₀) :
    ∃ (φ : E.A ⟶ A.A) (φ' : A.A ⟶ E.A) (hφ : φ ≫ A.f = E.f),
      FakeEllipticCurve.IsIsogenyPair d E A φ φ' ∧ FakeEllipticCurve.PreservesLevel E A φ hφ ∧
      g ≫ φ = φ₀ ≫ gA ∧ gA ≫ φ' = φ₀' ≫ g := by
  haveI := hq
  have hg' := hg
  have hgA' := hgA
  obtain ⟨sqE, -, hactE, -⟩ := hg'
  obtain ⟨sqA, -, hactA, hlevA⟩ := hgA'
  have wE : g ≫ E.f = E₀.f ≫ Spec.map (CommRingCat.ofHom q) := sqE.w
  haveI : IsIso g := sqE.isIso_fst_of_isIso hq
  haveI : IsIso gA := sqA.isIso_fst_of_isIso hq
  obtain ⟨hφ₀e, hφ₀'e, hmul, hmul', hact, hact', hcomp⟩ := h₀
  obtain ⟨hφ, φ_mul, φ_act⟩ := hom_transport q E A E₀ A₀ g hg gA hgA φ₀ hφ₀ hmul hact
  obtain ⟨hφ', φ'_mul, φ'_act⟩ := hom_transport q A E A₀ E₀ gA hgA g hg φ₀' hφ₀'e hmul' hact'
  refine ⟨inv g ≫ φ₀ ≫ gA, inv gA ≫ φ₀' ≫ g, hφ, ⟨hφ, hφ', φ_mul, φ'_mul, φ_act, φ'_act, ?_⟩, ?_, ?_, ?_⟩
  · intro hd
    obtain ⟨h1, h2⟩ := hcomp hd
    constructor
    · simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [← Category.assoc φ₀, h1, hactE, IsIso.inv_hom_id_assoc]
    · simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [← Category.assoc φ₀', h2, hactA, IsIso.inv_hom_id_assoc]
  · intro T t P hP
    have hP₀ : FactorsThrough E₀.lev
        (⟨P.1 ≫ inv g, liftPt_over q E E₀ g wE P⟩ :
          SchemeHomOver (t ≫ inv (Spec.map (CommRingCat.ofHom q))) E₀.f) :=
      CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia E q E₀ g hg _ _
        (by obtain ⟨R, hR⟩ := hP; exact ⟨R, by rw [hR, Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩)
    obtain ⟨R, hR⟩ := hlevA _ _ (hl₀ _ _ hP₀)
    refine ⟨R, ?_⟩
    rw [hR]
    simp only [mapPt_coe, Category.assoc]
  · simp only [IsIso.hom_inv_id_assoc]
  · simp only [IsIso.hom_inv_id_assoc]

end Transport

theorem isPullbackVia_congr {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type} [CommRing S] [CommRing S']
    {φ ψ : S →+* S'} (h : φ = ψ) {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
    (hE : FakeEllipticCurve.IsPullbackVia φ E E' g) : FakeEllipticCurve.IsPullbackVia ψ E E' g := by
  subst h; exact hE

end H1Aux

open H1Aux in
theorem solution
    {r N : ℕ}

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (B B₀ : Type) [CommRing B] [Algebra 𝒪 B] [CommRing B₀] [Algebra 𝒪 B₀]
    (p : B →ₐ[𝒪] B₀) (hp : Function.Surjective p) (hker : RingHom.ker (p : B →+* B₀) ≤ Ideal.span {algebraMap 𝒪 B π})
    (ψ : Onr →ₐ[𝒪] B)

    (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g)
    (ρ₀ : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀) :
    ∃ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀)
      (_ : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ρ ρ'),
      ∃ (ib : ρ₀.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ₀.gb ≫ (Iso.refl E₀.A).hom) (_ : ib ≫ ρ'.Eb.f = ρ₀.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₀.Ab ρ'.Ab uA) (_ : uA ≫ ρ₀.gA = ρ'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ρ'.φ ≫ uA ≫ ρ₀.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical

  have hle : Ideal.span {algebraMap 𝒪 B π} ≤ (Ideal.span {algebraMap 𝒪 B₀ π}).comap (p : B →+* B₀) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
      (by rw [show (p : B →+* B₀) (algebraMap 𝒪 B π) = algebraMap 𝒪 B₀ π from p.commutes π]
          exact Ideal.subset_span rfl)))
  set pbar := Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B₀ π}) (p : B →+* B₀) hle with hpbar
  have key : IsIso (Spec.map (CommRingCat.ofHom pbar)) := by
    have hsurj : Function.Surjective pbar := Ideal.quotientMap_surjective hp
    have hinj : Function.Injective pbar := by
      rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hpbar, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
      obtain ⟨c₀, hc₀⟩ := hx
      obtain ⟨c, rfl⟩ := hp c₀
      have hπ : algebraMap 𝒪 B₀ π = p (algebraMap 𝒪 B π) := (p.commutes π).symm
      have hmem : y - c * algebraMap 𝒪 B π ∈ RingHom.ker (p : B →+* B₀) := by
        rw [RingHom.mem_ker, map_sub, map_mul]
        show p y - p c * p (algebraMap 𝒪 B π) = 0
        rw [← hπ, hc₀]
        exact sub_self (p y)
      have := hker hmem
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have h2 : c * algebraMap 𝒪 B π ∈ Ideal.span {algebraMap 𝒪 B π} := Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      simpa using (Ideal.span {algebraMap 𝒪 B π}).add_mem this h2
    let e : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) ≃+* (B₀ ⧸ Ideal.span {algebraMap 𝒪 B₀ π}) :=
      RingEquiv.ofBijective pbar ⟨hinj, hsurj⟩
    have he' : CommRingCat.ofHom pbar = e.toCommRingCatIso.hom := rfl
    have : IsIso (CommRingCat.ofHom pbar) := by rw [he']; infer_instance
    infer_instance

  obtain ⟨Eb, gb, sqb, hmulb, hactb, hlevb, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E
  have hEb : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E Eb gb :=
    ⟨sqb, hmulb, hactb, hlevb⟩
  obtain ⟨Ab, gA, sqA, hmulA, hactA, hlevA, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀
  have hAb : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ Ab gA :=
    ⟨sqA, hmulA, hactA, hlevA⟩

  have h1 : FakeEllipticCurve.IsPullbackVia (pbar.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) E ρ₀.Eb (ρ₀.gb ≫ g) :=
    isPullbackVia_congr (Ideal.quotientMap_comp_mk hle).symm
      (CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (p : B →+* B₀)
        (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B₀ π})) E E₀ ρ₀.Eb g ρ₀.gb hg ρ₀.isPullback_Eb)
  obtain ⟨ub, hubg, hub⟩ := exists_factor _ pbar E Eb gb hEb ρ₀.Eb (ρ₀.gb ≫ g) h1
  have hleg : FakeEllipticCurve.Rigidification.residueLeg π (p.comp ψ) =
      pbar.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [FakeEllipticCurve.Rigidification.residueLeg, RingHom.comp_apply, hpbar, Ideal.quotientMap_mk]
    rfl
  have h2 : FakeEllipticCurve.IsPullbackVia (pbar.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)) A₀ ρ₀.Ab ρ₀.gA :=
    isPullbackVia_congr hleg ρ₀.isPullback_Ab
  obtain ⟨uA, huAg, huA⟩ := exists_factor _ pbar A₀ Ab gA hAb ρ₀.Ab ρ₀.gA h2

  obtain ⟨φ, φ', hφ, hpair, hlev, hgφ, -⟩ :=
    transport pbar key Eb Ab ρ₀.Eb ρ₀.Ab ub hub uA huA (r ^ ρ₀.d) ρ₀.φ ρ₀.φ' ρ₀.isIsogenyPair ρ₀.φ_over ρ₀.preservesLevel
  let ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E := ⟨Eb, gb, hEb, Ab, gA, hAb, ρ₀.d, φ, φ', hφ, hpair, hlev⟩
  refine ⟨ρ, ρ₀, ⟨ub, uA, hub, hubg, huA, huAg, rfl, hgφ⟩, 𝟙 _, by simp, by simp, 𝟙 _, isPullbackVia_refl _, by simp,
    0, 0, by simp only [Category.id_comp]⟩

#print axioms solution

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_ker_le_span
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_ker_le_span (solution)
