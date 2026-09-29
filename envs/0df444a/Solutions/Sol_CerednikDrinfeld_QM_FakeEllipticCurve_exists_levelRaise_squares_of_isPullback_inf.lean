-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelRaise_squares_of_isPullback_inf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c8c34dd7-65eb-5f78-bfcd-0968d7d58f16

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelRaise_squares_of_isPullback_inf
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace P2Aux

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem specMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

end P2Aux

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (K' K'' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (j : ↥K' →+* ↥K'') (hj : ∀ x : ↥K', ((j x : ↥K'') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (ι₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥O) (hι₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), (ι₀ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (j₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥K') (hj₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), ((j₀ x : ↥K') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (ι₁ : ↥(O.toSubring ⊓ K''.toSubring) →+* ↥O) (hι₁ : ∀ x : ↥(O.toSubring ⊓ K''.toSubring), (ι₁ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (j₁ : ↥(O.toSubring ⊓ K''.toSubring) →+* ↥K'') (hj₁ : ∀ x : ↥(O.toSubring ⊓ K''.toSubring), ((j₁ x : ↥K'') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (𝒜₀ : FakeEllipticCurve Λ N ↥(O.toSubring ⊓ K'.toSubring)) (𝒜 : FakeEllipticCurve Λ N ↥O)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (E₀ : FakeEllipticCurve Λ N ↥K')
    (p : 𝒜.A ⟶ 𝒜₀.A) (hp : CategoryTheory.IsPullback p 𝒜.f 𝒜₀.f (Spec.map (CommRingCat.ofHom ι₀)))
    (g₀ : E₀.A ⟶ 𝒜₀.A) (hg₀ : CategoryTheory.IsPullback g₀ E₀.f 𝒜₀.f (Spec.map (CommRingCat.ofHom j₀)))
    (hg₀_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K')) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g₀ =
        (𝒜₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom j₀))
          ⟨P.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, Q.2]⟩).1)
    (hg₀_act : ∀ x : ↥Λ, E₀.act x ≫ g₀ = g₀ ≫ 𝒜₀.act x)
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (gE' : E.A ⟶ E₀.A) (hgE' : CategoryTheory.IsPullback gE' E.f E₀.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ)))))
    (hgE'_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE' =
        (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ gE', by rw [Category.assoc, hgE'.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE', by rw [Category.assoc, hgE'.w, ← Category.assoc, Q.2]⟩).1)
    (hgE'_act : ∀ x : ↥Λ, E.act x ≫ gE' = gE' ≫ E₀.act x)
    (hcube : gE ≫ p = gE' ≫ g₀) :
    ∃ (𝒜₁ : FakeEllipticCurve Λ N ↥(O.toSubring ⊓ K''.toSubring)) (E₂ : FakeEllipticCurve Λ N ↥K'')
      (p₁ : 𝒜.A ⟶ 𝒜₁.A) (hp₁ : CategoryTheory.IsPullback p₁ 𝒜.f 𝒜₁.f (Spec.map (CommRingCat.ofHom ι₁)))
      (rE : E.A ⟶ E₂.A) (hrE : CategoryTheory.IsPullback rE E.f E₂.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ)))))
      (hrE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ rE =
        (E₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ rE, by rw [Category.assoc, hrE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ rE, by rw [Category.assoc, hrE.w, ← Category.assoc, Q.2]⟩).1)
      (hrE_act : ∀ x : ↥Λ, E.act x ≫ rE = rE ≫ E₂.act x)
      (gE₂ : E₂.A ⟶ 𝒜₁.A) (hgE₂ : CategoryTheory.IsPullback gE₂ E₂.f 𝒜₁.f (Spec.map (CommRingCat.ofHom j₁)))
      (hgE₂_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t' E₂.f),
      (E₂.L.mul t' P Q).1 ≫ gE₂ =
        (𝒜₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom j₁))
          ⟨P.1 ≫ gE₂, by rw [Category.assoc, hgE₂.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE₂, by rw [Category.assoc, hgE₂.w, ← Category.assoc, Q.2]⟩).1)
      (hgE₂_act : ∀ x : ↥Λ, E₂.act x ≫ gE₂ = gE₂ ≫ 𝒜₁.act x)
      (qE : E₂.A ⟶ E₀.A) (hqE : CategoryTheory.IsPullback qE E₂.f E₀.f (Spec.map (CommRingCat.ofHom j)))
      (hqE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t' E₂.f),
      (E₂.L.mul t' P Q).1 ≫ qE =
        (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom j))
          ⟨P.1 ≫ qE, by rw [Category.assoc, hqE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ qE, by rw [Category.assoc, hqE.w, ← Category.assoc, Q.2]⟩).1)
      (hqE_act : ∀ x : ↥Λ, E₂.act x ≫ qE = qE ≫ E₀.act x)
      , rE ≫ qE = gE' ∧ gE ≫ p₁ = rE ≫ gE₂ := by
  classical

  have hKle : K'.toSubring ≤ K''.toSubring := by
    intro x hx
    have h : (x : AlgebraicClosure ℚ) = ((j ⟨x, hx⟩ : ↥K'') : AlgebraicClosure ℚ) := (hj ⟨x, hx⟩).symm
    show x ∈ K''
    rw [h]
    exact (j ⟨x, hx⟩).2
  have hle : O.toSubring ⊓ K'.toSubring ≤ O.toSubring ⊓ K''.toSubring := inf_le_inf le_rfl hKle
  let κ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥(O.toSubring ⊓ K''.toSubring) := Subring.inclusion hle
  have hκ : ∀ x, (κ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := fun _ => rfl
  have hκι : ι₁.comp κ = ι₀ := by
    ext x
    show ((ι₁ (κ x) : ↥O) : AlgebraicClosure ℚ) = (ι₀ x : AlgebraicClosure ℚ)
    rw [hι₁, hι₀, hκ]
  have hκj : j₁.comp κ = j.comp j₀ := by
    ext x
    show ((j₁ (κ x) : ↥K'') : AlgebraicClosure ℚ) = ((j (j₀ x) : ↥K'') : AlgebraicClosure ℚ)
    rw [hj₁, hj, hj₀, hκ]
  have hOι₁ : O.subtype.comp ι₁ = (algebraMap ↥K'' (AlgebraicClosure ℚ)).comp j₁ := by
    ext x
    show (ι₁ x : AlgebraicClosure ℚ) = ((j₁ x : ↥K'') : AlgebraicClosure ℚ)
    rw [hι₁, hj₁]
  have hjalg : (algebraMap ↥K'' (AlgebraicClosure ℚ)).comp j = algebraMap ↥K' (AlgebraicClosure ℚ) := by
    ext x
    show ((j x : ↥K'') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)
    rw [hj]

  have sκι : Spec.map (CommRingCat.ofHom ι₀) = Spec.map (CommRingCat.ofHom ι₁) ≫ Spec.map (CommRingCat.ofHom κ) := by
    rw [← hκι, P2Aux.specMap_comp]
  have sκj : Spec.map (CommRingCat.ofHom j₁) ≫ Spec.map (CommRingCat.ofHom κ) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom j₀) := by
    rw [← P2Aux.specMap_comp, ← P2Aux.specMap_comp, hκj]
  have sOι₁ : Spec.map (CommRingCat.ofHom O.subtype) ≫ Spec.map (CommRingCat.ofHom ι₁) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom j₁) := by
    rw [← P2Aux.specMap_comp, ← P2Aux.specMap_comp, hOι₁]
  have sjalg : Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom j) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))) := by
    rw [← P2Aux.specMap_comp, hjalg]

  obtain ⟨𝒜₁, q₁, hq₁, hq₁_mul, hq₁_act, -, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff κ 𝒜₀
  obtain ⟨E₂, gE₂, hgE₂, hgE₂_mul, hgE₂_act, -, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff j₁ 𝒜₁

  have wp₁ : p ≫ 𝒜₀.f = (𝒜.f ≫ Spec.map (CommRingCat.ofHom ι₁)) ≫ Spec.map (CommRingCat.ofHom κ) := by
    rw [hp.w, Category.assoc, sκι]
  let p₁ : 𝒜.A ⟶ 𝒜₁.A := hq₁.lift p (𝒜.f ≫ Spec.map (CommRingCat.ofHom ι₁)) wp₁
  have hp₁q₁ : p₁ ≫ q₁ = p := hq₁.lift_fst _ _ _
  have hp₁f : p₁ ≫ 𝒜₁.f = 𝒜.f ≫ Spec.map (CommRingCat.ofHom ι₁) := hq₁.lift_snd _ _ _
  have hp₁ : CategoryTheory.IsPullback p₁ 𝒜.f 𝒜₁.f (Spec.map (CommRingCat.ofHom ι₁)) := by
    have big : CategoryTheory.IsPullback (p₁ ≫ q₁) 𝒜.f 𝒜₀.f
        (Spec.map (CommRingCat.ofHom ι₁) ≫ Spec.map (CommRingCat.ofHom κ)) := by
      rw [hp₁q₁, ← sκι]; exact hp
    exact big.of_right hp₁f hq₁

  have wrE : (gE ≫ p₁) ≫ 𝒜₁.f =
      (E.f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ)))) ≫ Spec.map (CommRingCat.ofHom j₁) := by
    rw [Category.assoc, hp₁f, ← Category.assoc, hgE.w, Category.assoc, sOι₁, Category.assoc]
  let rE : E.A ⟶ E₂.A := hgE₂.lift (gE ≫ p₁) (E.f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ)))) wrE
  have hrEg : rE ≫ gE₂ = gE ≫ p₁ := hgE₂.lift_fst _ _ _
  have hrEf : rE ≫ E₂.f = E.f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))) := hgE₂.lift_snd _ _ _
  have hrE : CategoryTheory.IsPullback rE E.f E₂.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ)))) := by
    have big : CategoryTheory.IsPullback (rE ≫ gE₂) E.f 𝒜₁.f
        (Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom j₁)) := by
      rw [hrEg, ← sOι₁]; exact hgE.paste_horiz hp₁
    exact big.of_right hrEf hgE₂

  have wqE : (gE₂ ≫ q₁) ≫ 𝒜₀.f = (E₂.f ≫ Spec.map (CommRingCat.ofHom j)) ≫ Spec.map (CommRingCat.ofHom j₀) := by
    rw [Category.assoc, hq₁.w, ← Category.assoc, hgE₂.w, Category.assoc, sκj, Category.assoc]
  let qE : E₂.A ⟶ E₀.A := hg₀.lift (gE₂ ≫ q₁) (E₂.f ≫ Spec.map (CommRingCat.ofHom j)) wqE
  have hqEg : qE ≫ g₀ = gE₂ ≫ q₁ := hg₀.lift_fst _ _ _
  have hqEf : qE ≫ E₀.f = E₂.f ≫ Spec.map (CommRingCat.ofHom j) := hg₀.lift_snd _ _ _
  have hqE : CategoryTheory.IsPullback qE E₂.f E₀.f (Spec.map (CommRingCat.ofHom j)) := by
    have big : CategoryTheory.IsPullback (qE ≫ g₀) E₂.f 𝒜₀.f
        (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom j₀)) := by
      rw [hqEg, ← sκj]; exact hgE₂.paste_horiz hq₁
    exact big.of_right hqEf hg₀

  have hcube' : rE ≫ gE₂ ≫ q₁ = gE' ≫ g₀ := by
    rw [← Category.assoc, hrEg, Category.assoc, hp₁q₁, hcube]
  have heq1 : rE ≫ qE = gE' := by
    apply hg₀.hom_ext
    · rw [Category.assoc, hqEg, hcube']
    · rw [Category.assoc, hqEf, ← Category.assoc, hrEf, Category.assoc, sjalg, hgE'.w]
  have heq2 : gE ≫ p₁ = rE ≫ gE₂ := hrEg.symm

  have hrE_act : ∀ x : ↥Λ, E.act x ≫ rE = rE ≫ E₂.act x := by
    intro x
    apply hgE₂.hom_ext
    · apply hq₁.hom_ext
      · have eL : ((E.act x ≫ rE) ≫ gE₂) ≫ q₁ = gE' ≫ g₀ ≫ 𝒜₀.act x := by
          simp only [Category.assoc, hcube']
          rw [reassoc_of% (hgE'_act x), hg₀_act x]
        have eR : ((rE ≫ E₂.act x) ≫ gE₂) ≫ q₁ = gE' ≫ g₀ ≫ 𝒜₀.act x := by
          simp only [Category.assoc]
          rw [reassoc_of% (hgE₂_act x), hq₁_act x, reassoc_of% hcube']
        rw [eL, eR]
      · simp only [Category.assoc]
        rw [hgE₂.w, reassoc_of% (E₂.act_over x), reassoc_of% hrEf, reassoc_of% (E.act_over x)]
    · simp only [Category.assoc]
      rw [E₂.act_over x, hrEf, reassoc_of% (E.act_over x)]
  have hrE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ rE =
        (E₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ rE, by rw [Category.assoc, hrE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ rE, by rw [Category.assoc, hrE.w, ← Category.assoc, Q.2]⟩).1 := by
    intro T t' P Q
    apply hgE₂.hom_ext
    · apply hq₁.hom_ext
      · have eL : (((E.L.mul t' P Q).1 ≫ rE) ≫ gE₂) ≫ q₁ = ((E.L.mul t' P Q).1 ≫ gE') ≫ g₀ := by
          simp only [Category.assoc, hcube']
        rw [eL, hgE'_mul, hg₀_mul, hgE₂_mul, hq₁_mul]
        refine P2Aux.mul_val_congr 𝒜₀.L ?_ _ _ _ _ ?_ ?_
        · simp only [Category.assoc]
          rw [sκj, reassoc_of% sjalg]
        · simp only [Category.assoc, hcube']
        · simp only [Category.assoc, hcube']
      · simp only [Category.assoc]
        rw [hgE₂.w, reassoc_of% hrEf, reassoc_of% (E.L.mul t' P Q).2, reassoc_of% (E₂.L.mul _ _ _).2,
          Category.assoc]
    · rw [(E₂.L.mul _ _ _).2, Category.assoc, hrEf, reassoc_of% (E.L.mul t' P Q).2]

  have hqE_act : ∀ x : ↥Λ, E₂.act x ≫ qE = qE ≫ E₀.act x := by
    intro x
    apply hg₀.hom_ext
    · simp only [Category.assoc]
      rw [hqEg, reassoc_of% (hgE₂_act x), hq₁_act x, hg₀_act x, reassoc_of% hqEg]
    · simp only [Category.assoc]
      rw [E₀.act_over x, hqEf, reassoc_of% (E₂.act_over x)]
  have hqE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t' E₂.f),
      (E₂.L.mul t' P Q).1 ≫ qE =
        (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom j))
          ⟨P.1 ≫ qE, by rw [Category.assoc, hqE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ qE, by rw [Category.assoc, hqE.w, ← Category.assoc, Q.2]⟩).1 := by
    intro T t' P Q
    apply hg₀.hom_ext
    · have eL : ((E₂.L.mul t' P Q).1 ≫ qE) ≫ g₀ = ((E₂.L.mul t' P Q).1 ≫ gE₂) ≫ q₁ := by
        simp only [Category.assoc, hqEg]
      rw [eL, hgE₂_mul, hq₁_mul, hg₀_mul]
      refine P2Aux.mul_val_congr 𝒜₀.L ?_ _ _ _ _ ?_ ?_
      · simp only [Category.assoc, sκj]
      · simp only [Category.assoc, hqEg]
      · simp only [Category.assoc, hqEg]
    · rw [(E₀.L.mul _ _ _).2, Category.assoc, hqEf, reassoc_of% (E₂.L.mul t' P Q).2]
  exact ⟨𝒜₁, E₂, p₁, hp₁, rE, hrE, hrE_mul, hrE_act, gE₂, hgE₂, hgE₂_mul, hgE₂_act, qE, hqE, hqE_mul, hqE_act,
    heq1, heq2⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelRaise_squares_of_isPullback_inf
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelRaise_squares_of_isPullback_inf (solution)
