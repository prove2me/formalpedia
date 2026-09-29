-- Prove2me | solution 1 for CerednikDrinfeld.QM.RigidifiedPairClass.map_ptR_eq_ptR_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b9ed7ec0-4fa5-5b5b-aa11-7c13914dca57

import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_map_ptR_eq_ptR_of_isPullbackVia
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open GoodReductionJacobian

namespace EngM7R2

theorem mapPt_refl {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (h : (Iso.refl A).hom ≫ f = f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt (Iso.refl A).hom h P = P :=
  Subtype.ext (by rw [mapPt_coe, Iso.refl_hom, Category.comp_id])

theorem isoVia_refl {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n : ℕ} {S : Type} [CommRing S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (h : (Iso.refl u.1.A).hom ≫ u.1.f = u.1.f) :
    FakeEllipticCurve.WithFullLevel.IsoVia u u (Iso.refl u.1.A) h := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [mapPt_refl, mapPt_refl, mapPt_refl]
  · intro x
    rw [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro T t P
    rw [mapPt_refl]
  · rw [mapPt_refl]

theorem isoVia_refl_bare {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (h : (Iso.refl E.A).hom ≫ E.f = E.f) :
    FakeEllipticCurve.IsoVia E E (Iso.refl E.A) h := by
  refine ⟨?_, ?_, ?_⟩
  · intro T t P Q
    rw [mapPt_refl, mapPt_refl, mapPt_refl]
  · intro x
    rw [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro T t P
    rw [mapPt_refl]

theorem isLocalizationAway_one (R : Type) [CommRing R] : IsLocalization.Away (1 : R) R :=
  IsLocalization.of_le_isUnit (fun x hx => by
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 hx
    rw [← hk, one_pow]
    exact isUnit_one)

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) (P' Q' : SchemeHomOver t₂ f) (hP : P'.1 = P.1) (hQ : Q'.1 = Q.1) :
    (L.mul t₂ P' Q').1 = (L.mul t₁ P Q).1 := by
  subst h
  obtain ⟨P, hP0⟩ := P
  obtain ⟨Q, hQ0⟩ := Q
  obtain ⟨P', hP0'⟩ := P'
  obtain ⟨Q', hQ0'⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem isPullbackVia_id_of_isoVia {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E E' : FakeEllipticCurve Λ N S) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (h : FakeEllipticCurve.IsoVia E E' i hi) :
    FakeEllipticCurve.IsPullbackVia (RingHom.id S) E' E i.hom := by
  have e1 : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have hpb : IsPullback i.hom E.f E'.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [e1]
    exact IsPullback.of_horiz_isIso ⟨by rw [hi, Category.comp_id]⟩
  refine ⟨hpb, ?_, h.2.1, ?_⟩
  · intro T t' P Q
    have key := congrArg Subtype.val (h.1 t' P Q)
    simp only [mapPt_coe] at key
    rw [key]
    symm
    apply mul_val_congr
    · rw [e1, Category.comp_id]
    · rfl
    · rfl
  · intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := (h.2.2 t' P).1 hP
    exact ⟨P₀, hP₀⟩

theorem isPullbackVia_id {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E (𝟙 E.A) :=
  isPullbackVia_id_of_isoVia E E (Iso.refl E.A) (by rw [Iso.refl_hom, Category.id_comp]) (isoVia_refl_bare E _)

end EngM7R2

theorem solution
    {r N : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) g)
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })
    (hmap : RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf)

    (hTnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S')
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
      (g' : u'.1.A ⟶ u.1.A), FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g' →
      (u'.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
      (tM S' u').1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (tM S u).1)

    (hXnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
      (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
      (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
      (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
      (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
      (g' : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g'),
      (u'.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
      FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g' hg ρ ρ' →
        ∃ hd : ρ'.d = ρ.d,
          (xOf S' _ hψS' u' ρ').1 ≫ eqToHom (congrArg X hd) =
            Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1)

    (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
    (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
    (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
    (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
    (g' : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g')
    (hP : (u'.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1)
    (hρ : FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g' hg ρ ρ') :
    (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap).map φ
        (RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap S ψS hψS u ρ) =
      RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ' := by
  classical
  show Quot.mk _ (RigidifiedPairClass.Pt.map φ _) = Quot.mk _ _
  apply Quot.sound
  refine ⟨?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (tM S u).1 = (tM S' u').1
    exact (hTnat S S' φ u u' g' hg hP).symm

  set I' : Ideal S' := Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)} with hI'
  let pA : S' →ₐ[C] S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)} := Ideal.Quotient.mkₐ C _
  have h0 : algebraMap C (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}) (algebraMap 𝒪 C π) = 0 := by
    rw [IsScalarTower.algebraMap_apply C S' (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}), Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hψL : ((pA.restrictScalars 𝒪).comp ((φ.restrictScalars 𝒪).comp ψS)) =
      (IsScalarTower.toAlgHom 𝒪 C (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)})).comp ψ := by
    rw [hψS']
    apply AlgHom.ext; intro x; rfl

  have eSS : Spec.map (CommRingCat.ofHom (algebraMap (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)})
      (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}))) = 𝟙 _ := by
    have : algebraMap (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}) (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}) = RingHom.id _ :=
      RingHom.ext fun _ => rfl
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have hid : (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans
        (RingEquiv.quotientBot (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}))).toRingHom).comp
        (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) pA) = RingHom.id _ := by
    apply RingHom.ext
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    rfl
  have heS : Spec.map (CommRingCat.ofHom (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans
        (RingEquiv.quotientBot (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}))).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) pA)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hid, CommRingCat.ofHom_id, Spec.map_id]

  obtain ⟨ub, gb, hgpb, hgmul, hgact, hglev, -, hgP⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (((pA.restrictScalars 𝒪 : S' →ₐ[𝒪] (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}))) : S' →+* (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)})) u'
  have hgb : FakeEllipticCurve.IsPullbackVia (((pA.restrictScalars 𝒪 : S' →ₐ[𝒪] (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}))) : S' →+* (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)})) u'.1 ub.1 gb := ⟨hgpb, hgmul, hgact, hglev⟩
  obtain ⟨ρb, hρb⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia 𝒪 π Onr Λ A₀ S' _
      (pA.restrictScalars 𝒪) ((φ.restrictScalars 𝒪).comp ψS) u'.1 ub.1 gb hgb ρ'

  have hdρb : ρb.d = ρ'.d := by obtain ⟨_, _, _, _, _, _, hd, _⟩ := hρb; exact hd
  have hdρ' : ρ'.d = ρ.d := by obtain ⟨_, _, _, _, _, _, hd, _⟩ := hρ; exact hd

  obtain ⟨hd1, hnat1⟩ := hXnat S S' φ ψS hψS hψS' u u' ρ ρ' g' hg hP hρ
  obtain ⟨hd2, hnat2⟩ := hXnat S' _ pA ((φ.restrictScalars 𝒪).comp ψS) hψS' hψL u' ub ρ' ρb gb hgb hgP hρb

  have key : ∀ (ψL : Onr →ₐ[𝒪] (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}))
      (e : (pA.restrictScalars 𝒪).comp ((φ.restrictScalars 𝒪).comp ψS) = ψL)
      (hψL' : ψL = (IsScalarTower.toAlgHom 𝒪 C (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)})).comp ψ),
      ∃ (v v' : FakeEllipticCurve.WithFullLevel Λ N n (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}))
        (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψL v.1) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψL v'.1)
        (hd : ϱ.d = ρ.d) (hd' : ϱ'.d = ρ'.d)
        (i₀ : v.1.A ≅ v'.1.A) (hi : i₀.hom ≫ v'.1.f = v.1.f) (_ : FakeEllipticCurve.WithFullLevel.IsoVia v v' i₀ hi)
        (_ : (∃ (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ.gb ≫ i₀.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
            (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ.gA = ϱ'.gA)
            (i₁ j₁ : ℕ),
            ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)),
        (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf ρ.d _ ψL hψL' v ϱ hd h0).1 =
            Spec.map (CommRingCat.ofHom (algebraMap (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}) (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}))) ≫
              (Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1) ∧
          (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf ρ'.d _ ψL hψL' v' ϱ' hd' h0).1 =
            Spec.map (CommRingCat.ofHom (algebraMap (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}) (S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}))) ≫
              (xOf S' _ hψS' u' ρ').1 := by
    intro ψL e hψL'
    subst e
    refine ⟨ub, ub, ρb, ρb, hdρb.trans hdρ', hdρb, Iso.refl _, (by rw [Iso.refl_hom, Category.id_comp]), EngM7R2.isoVia_refl ub _,
      ⟨𝟙 _, (by rw [Iso.refl_hom, Category.id_comp, Category.comp_id]), (by rw [Category.id_comp]), 𝟙 _, EngM7R2.isPullbackVia_id ρb.Ab,
        (by rw [Category.id_comp]), 0, 0, (by rw [Category.id_comp, Category.id_comp])⟩, ?_, ?_⟩
    ·
      have hdd : (hdρb.trans hdρ' : ρb.d = ρ.d) = hd2.trans hd1 := rfl
      show Spec.map (CommRingCat.ofHom _) ≫ (xOf _ _ hψL' ub ρb).1 ≫ eqToHom (congrArg X (hdρb.trans hdρ')) = _
      rw [eSS, Category.id_comp, hdd]
      rw [show eqToHom (congrArg X (hd2.trans hd1)) = eqToHom (congrArg X hd2) ≫ eqToHom (congrArg X hd1) from (eqToHom_trans _ _).symm]
      rw [← Category.assoc (xOf _ _ hψL' ub ρb).1, hnat2, Category.assoc, hnat1, ← Category.assoc, heS, Category.id_comp]
    · show Spec.map (CommRingCat.ofHom _) ≫ (xOf _ _ hψL' ub ρb).1 ≫ eqToHom (congrArg X hdρb) = _
      have hdd : hdρb = hd2 := rfl
      rw [eSS, Category.id_comp, hdd, hnat2, ← Category.assoc, heS, Category.id_comp]
  obtain ⟨v, v', ϱ, ϱ', hd, hd', i₀, hi, hvia, hcorr, leg1, leg2⟩ := key _ hψL rfl
  refine ⟨1, fun _ => 1, ?_, fun k => ⟨S' ⧸ Ideal.span {algebraMap C S' (algebraMap 𝒪 C π)}, inferInstance, inferInstance,
    EngM7R2.isLocalizationAway_one _, inferInstance, inferInstance, inferInstance, inferInstance, h0,
    v, v', ϱ, ϱ', hd, hd', i₀, hi, hvia, hcorr, leg1, leg2⟩⟩
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one

end S_CerednikDrinfeld_QM_RigidifiedPairClass_map_ptR_eq_ptR_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_map_ptR_eq_ptR_of_isPullbackVia (solution)
