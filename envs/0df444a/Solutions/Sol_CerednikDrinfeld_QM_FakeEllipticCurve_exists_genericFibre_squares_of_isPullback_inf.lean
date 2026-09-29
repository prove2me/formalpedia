-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_genericFibre_squares_of_isPullback_inf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/751fbf56-9b34-5c35-9033-2f59488de42f

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_genericFibre_squares_of_isPullback_inf
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (K' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ι₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥O)
    (hι₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), (ι₀ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (j₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥K')
    (hj₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), ((j₀ x : ↥K') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (𝒜₀ : FakeEllipticCurve Λ N ↥(O.toSubring ⊓ K'.toSubring)) (𝒜 : FakeEllipticCurve Λ N ↥O)
    (h𝒜₀ : FakeEllipticCurve.IsPullback ι₀ 𝒜₀ 𝒜)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x) :
    ∃ (E₀ : FakeEllipticCurve Λ N ↥K')
      (p : 𝒜.A ⟶ 𝒜₀.A) (hp : CategoryTheory.IsPullback p 𝒜.f 𝒜₀.f (Spec.map (CommRingCat.ofHom ι₀)))
      (g₀ : E₀.A ⟶ 𝒜₀.A) (hg₀ : CategoryTheory.IsPullback g₀ E₀.f 𝒜₀.f (Spec.map (CommRingCat.ofHom j₀)))
      (gE' : E.A ⟶ E₀.A)
      (hgE' : CategoryTheory.IsPullback gE' E.f E₀.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t' 𝒜.f),
        (𝒜.L.mul t' P Q).1 ≫ p =
          (𝒜₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ι₀))
            ⟨P.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, 𝒜.act x ≫ p = p ≫ 𝒜₀.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K')) (P Q : SchemeHomOver t' E₀.f),
        (E₀.L.mul t' P Q).1 ≫ g₀ =
          (𝒜₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom j₀))
            ⟨P.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₀.act x ≫ g₀ = g₀ ≫ 𝒜₀.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ gE' =
          (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))
            ⟨P.1 ≫ gE', by rw [Category.assoc, hgE'.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gE', by rw [Category.assoc, hgE'.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ gE' = gE' ≫ E₀.act x) ∧
      gE ≫ p = gE' ≫ g₀ := by
  classical

  obtain ⟨E₀, g₀, hg₀, hg₀_mul, hg₀_act, -, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff j₀ 𝒜₀
  obtain ⟨p, hp, hp_mul, hp_act, -⟩ := h𝒜₀

  have hring : O.subtype.comp ι₀ = (algebraMap ↥K' (AlgebraicClosure ℚ)).comp j₀ := by
    ext x; show ((ι₀ x : ↥O) : AlgebraicClosure ℚ) = ((j₀ x : ↥K') : AlgebraicClosure ℚ); rw [hι₀, hj₀]
  have hSpec : Spec.map (CommRingCat.ofHom O.subtype) ≫ Spec.map (CommRingCat.ofHom ι₀) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom j₀) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]

  have hw : (gE ≫ p) ≫ 𝒜₀.f = (E.f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ)))) ≫
      Spec.map (CommRingCat.ofHom j₀) := by
    rw [Category.assoc, hp.w, ← Category.assoc, hgE.w, Category.assoc, hSpec, Category.assoc]
  let gE' : E.A ⟶ E₀.A := hg₀.lift (gE ≫ p) (E.f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ)))) hw
  have hfst : gE' ≫ g₀ = gE ≫ p := hg₀.lift_fst _ _ _
  have hsnd : gE' ≫ E₀.f = E.f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))) := hg₀.lift_snd _ _ _

  have hbig : IsPullback (gE ≫ p) E.f 𝒜₀.f
      (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom j₀)) := by
    rw [← hSpec]; exact hgE.paste_horiz hp
  have hgE' : IsPullback gE' E.f E₀.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ)))) := by
    refine IsPullback.of_right ?_ hsnd hg₀
    rw [hfst]; exact hbig

  have mul0_congr : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of ↥(O.toSubring ⊓ K'.toSubring))} (h : t₁ = t₂)
      (P₁ Q₁ : SchemeHomOver t₁ 𝒜₀.f) (P₂ Q₂ : SchemeHomOver t₂ 𝒜₀.f), P₁.1 = P₂.1 → Q₁.1 = Q₂.1 →
      (𝒜₀.L.mul t₁ P₁ Q₁).1 = (𝒜₀.L.mul t₂ P₂ Q₂).1 := by
    rintro T t₁ t₂ rfl P₁ Q₁ P₂ Q₂ hP hQ
    obtain rfl : P₁ = P₂ := Subtype.ext hP; obtain rfl : Q₁ = Q₂ := Subtype.ext hQ; rfl
  refine ⟨E₀, p, hp, g₀, hg₀, gE', hgE', hp_mul, hp_act, hg₀_mul, hg₀_act, ?_, ?_, hfst.symm⟩
  ·
    intro T t' P Q
    apply hg₀.hom_ext
    · rw [Category.assoc, hfst, ← Category.assoc, hgE_mul, hp_mul, hg₀_mul]
      refine mul0_congr (by rw [Category.assoc, hSpec, Category.assoc]) _ _ _ _ ?_ ?_
      · show (P.1 ≫ gE) ≫ p = (P.1 ≫ gE') ≫ g₀
        rw [Category.assoc, Category.assoc, hfst]
      · show (Q.1 ≫ gE) ≫ p = (Q.1 ≫ gE') ≫ g₀
        rw [Category.assoc, Category.assoc, hfst]
    · refine Eq.trans ?_ ((E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ)))) _ _).2).symm
      rw [Category.assoc, hsnd, ← Category.assoc, (E.L.mul t' P Q).2]
  ·
    intro x
    apply hg₀.hom_ext
    · simp only [Category.assoc]
      rw [hfst, reassoc_of% (hgE_act x), hp_act, hg₀_act, reassoc_of% hfst]
    · simp only [Category.assoc]
      rw [hsnd, reassoc_of% (E.act_over x), E₀.act_over, hsnd]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_genericFibre_squares_of_isPullback_inf
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_genericFibre_squares_of_isPullback_inf (solution)
