-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_iso_quotient_pullback_of_flat_pointCompat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/de6ac020-3df1-5f2c-a51f-965f14e1da26

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_pullback_equivariant_of_isLevelTwistAction
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_quotient_pullback_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_iso_quotient_pullback_of_flat_pointCompat
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open CategoryTheory.Limits

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ) [NeZero N] (hm : 3 ≤ m)
    {B₀ 𝒪 : Type} [CommRing B₀] [CommRing 𝒪] (i : B₀ →+* 𝒪) (hi : Flat (Spec.map (CommRingCat.ofHom i)))
    (hN : IsUnit ((N : ℕ) : B₀)) (hm' : IsUnit ((m : ℕ) : B₀))

    {M₀ : Scheme.{0}} {πM₀ : M₀ ⟶ Spec (CommRingCat.of B₀)}
    {ptF₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM₀}
    (hM₀ : IsFineModuli Λ N m M₀ πM₀ ptF₀)
    {G₀ : Type} [Group G₀] [Finite G₀] {ρ₀ : G₀ →* Aut M₀} {χ₀ : G₀ → ↥Λ} (hρ₀ : IsLevelTwistAction Λ N m M₀ πM₀ ptF₀ G₀ ρ₀ χ₀)
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] [Finite G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)

    (H : Type) [Group H] [Finite H] (φ₀ : H →* G₀) (hφ₀ : Function.Injective φ₀) (φ : H →* G) (hφ : Function.Injective φ)
    (hlabel : ∀ h : H, ∃ y : ↥Λ, (χ₀ (φ₀ h) : ℍ[ℚ, a, b]) - (χ (φ h) : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))

    (X₀ : Scheme.{0}) (πX₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (π₀ : M₀ ⟶ X₀) (hπX₀ : π₀ ≫ πX₀ = πM₀)
    (hπ₀ : ∀ h : H, (ρ₀ (φ₀ h)).hom ≫ π₀ = π₀)
    (hint₀ : IsIntegralHom π₀) (haff₀ : IsAffineHom π₀) (hsurj₀ : Function.Surjective π₀.base)
    (horbit₀ : ∀ x x' : M₀, π₀.base x = π₀.base x' ↔ ∃ h : H, (ρ₀ (φ₀ h)).hom.base x = x')
    (hsec₀ : ∀ V : X₀.Opens, Function.Injective (π₀.app V))
    (hinv₀ : ∀ V : X₀.Opens, Set.range (π₀.app V) =
      {s | ∀ h : H, (ρ₀ (φ₀ h)).hom.appLE (π₀ ⁻¹ᵁ V) (π₀ ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ₀ h]) s = s})
    (hcat₀ : ∀ (T : Scheme.{0}) (f : M₀ ⟶ T), (∀ h : H, (ρ₀ (φ₀ h)).hom ≫ f = f) → ∃! f' : X₀ ⟶ T, π₀ ≫ f' = f)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of 𝒪)) (π : M ⟶ X) (hπX : π ≫ πX = πM)
    (hπ : ∀ h : H, (ρ (φ h)).hom ≫ π = π)
    (hint : IsIntegralHom π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ (φ h)).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ (φ h)).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hcat : ∀ (T : Scheme.{0}) (f : M ⟶ T), (∀ h : H, (ρ (φ h)).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f) :
    ∃ (eM : M ⟶ Limits.pullback πM₀ (Spec.map (CommRingCat.ofHom i))) (e : X ⟶ Limits.pullback πX₀ (Spec.map (CommRingCat.ofHom i))),
      IsIso eM ∧ IsIso e ∧
      eM ≫ Limits.pullback.snd πM₀ (Spec.map (CommRingCat.ofHom i)) = πM ∧
      e ≫ Limits.pullback.snd πX₀ (Spec.map (CommRingCat.ofHom i)) = πX ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N m S),
        (ptF S s u).1 ≫ eM ≫ Limits.pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i)) =
          (ptF₀ S (s ≫ Spec.map (CommRingCat.ofHom i)) u).1) ∧
      π ≫ e = eM ≫ Limits.pullback.lift (Limits.pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i)) ≫ π₀)
        (Limits.pullback.snd πM₀ (Spec.map (CommRingCat.ofHom i))) (by rw [Category.assoc, hπX₀, Limits.pullback.condition]) := by
  classical
  obtain ⟨eM, heMiso, heMsnd, heMeq, heMpt⟩ :=
    CerednikDrinfeld.QM.IsFineModuli.exists_iso_pullback_equivariant_of_isLevelTwistAction hqq' hB Λ hΛ N m hm i hi hN hm'
      hM₀ hρ₀ hM hρ H φ₀ hφ₀ φ hφ hlabel
  haveI := heMiso
  have hgM : IsPullback (eM ≫ pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i))) πM πM₀ (Spec.map (CommRingCat.ofHom i)) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso eM) (by simp) (by simpa using heMsnd)
    rw [Category.assoc, pullback.condition, ← Category.assoc, heMsnd]
  have hρg : ∀ h : H, (ρ.comp φ h).hom ≫ (eM ≫ pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i))) =
      (eM ≫ pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i))) ≫ (ρ₀.comp φ₀ h).hom := by
    intro h
    have h2 := congrArg (· ≫ pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i))) (heMeq h)
    simp only [Category.assoc, pullback.lift_fst] at h2
    simpa only [MonoidHom.comp_apply, Category.assoc] using h2
  obtain ⟨e, heiso, hesnd, hsq⟩ :=
    AlgebraicGeometry.Scheme.exists_iso_quotient_pullback_of_flat i hi πM₀ πX₀ π₀ hπX₀ (ρ₀.comp φ₀)
      (fun h => hρ₀.over_base (φ₀ h)) hπ₀ hint₀ haff₀ hsurj₀ horbit₀ hsec₀ hinv₀ hcat₀
      πM (eM ≫ pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i))) hgM (ρ.comp φ) (fun h => hρ.over_base (φ h)) hρg
      πX π hπX hπ hint haff hsurj horbit hsec hinv hcat
  refine ⟨eM, e, heMiso, heiso, heMsnd, hesnd, heMpt, ?_⟩
  rw [hsq]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
  · simp only [Category.assoc, pullback.lift_snd, heMsnd]

end S_CerednikDrinfeld_QM_IsFineModuli_exists_iso_quotient_pullback_of_flat_pointCompat
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_iso_quotient_pullback_of_flat_pointCompat (solution)
