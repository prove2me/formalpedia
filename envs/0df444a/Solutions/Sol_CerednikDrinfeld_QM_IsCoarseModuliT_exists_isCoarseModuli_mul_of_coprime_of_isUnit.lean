-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/39096ed7-7a33-5903-a575-f68f8b182a1f

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_forall_factorsThrough_iff_of_mul_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_iso_of_forall_factorsThrough_iff_mul
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isPullback_of_isPullback_of_forall_factorsThrough_iff_mul
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_withExtraLevel_isPullback_of_forall_factorsThrough_iff_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_isCoarseModuli_mul_of_coprime_of_isUnit
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace PairsLevel

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ}

def Splits {S : Type} [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (E' : FakeEllipticCurve Λ (N * ℓ) S) : Prop :=
  ∃ (e : u.1.A ≅ E'.A) (he : e.hom ≫ E'.f = u.1.f),
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔
        FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t N (mapPt e.hom he P) = E'.L.one t) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P ↔
        FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t ℓ (mapPt e.hom he P) = E'.L.one t)

theorem mapPt_id {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (h : (Iso.refl A).hom ≫ f = f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt (Iso.refl A).hom h P = P :=
  Subtype.ext (Category.comp_id _)

theorem iso_refl {S : Type} [CommRing S] (E : FakeEllipticCurve Λ (N * ℓ) S) : FakeEllipticCurve.Iso E E := by
  refine ⟨Iso.refl _, Category.id_comp _, ?_, ?_, ?_⟩
  · intro T t P Q; rw [mapPt_id, mapPt_id, mapPt_id]
  · intro x; simp
  · intro T t P; rw [mapPt_id]

theorem isoT_refl {S : Type} [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) : FakeEllipticCurve.WithExtraLevel.Iso u u := by
  refine ⟨Iso.refl _, Category.id_comp _, ?_, ?_, ?_, ?_⟩
  · intro T t P Q; rw [mapPt_id, mapPt_id, mapPt_id]
  · intro x; simp
  · intro T t P; rw [mapPt_id]
  · intro T t P; rw [mapPt_id]

theorem isoT_of_splits {S : Type} [CommRing S] {E₁ E₂ : FakeEllipticCurve Λ (N * ℓ) S} (h : FakeEllipticCurve.Iso E₁ E₂)
    {u₁ u₂ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S} (h₁ : Splits u₁ E₁) (h₂ : Splits u₂ E₂) :
    FakeEllipticCurve.WithExtraLevel.Iso u₁ u₂ := by
  obtain ⟨e₁, he₁, a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨e₂, he₂, a₂, b₂, c₂, d₂⟩ := h₂
  exact CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_iso_of_forall_factorsThrough_iff_mul E₁ E₂ h
    u₁ e₁ he₁ a₁ b₁ c₁ d₁ u₂ e₂ he₂ a₂ b₂ c₂ d₂

theorem iso_of_splits (hNℓ : N.Coprime ℓ) {S : Type} [CommRing S] {u₁ u₂ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S}
    (h : FakeEllipticCurve.WithExtraLevel.Iso u₁ u₂)
    {E₁ E₂ : FakeEllipticCurve Λ (N * ℓ) S} (h₁ : Splits u₁ E₁) (h₂ : Splits u₂ E₂) :
    FakeEllipticCurve.Iso E₁ E₂ := by
  obtain ⟨e₁, he₁, a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨e₂, he₂, a₂, b₂, c₂, d₂⟩ := h₂
  exact CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul hNℓ u₁ u₂ h
    E₁ e₁ he₁ a₁ b₁ c₁ d₁ E₂ e₂ he₂ a₂ b₂ c₂ d₂

theorem isPullbackT_of_splits {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {E : FakeEllipticCurve Λ (N * ℓ) S} {E' : FakeEllipticCurve Λ (N * ℓ) S'} (h : FakeEllipticCurve.IsPullback φ E E')
    {u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S} {u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'}
    (h₁ : Splits u E) (h₂ : Splits u' E') : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' := by
  obtain ⟨e₁, he₁, a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨e₂, he₂, a₂, b₂, c₂, d₂⟩ := h₂
  exact CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isPullback_of_isPullback_of_forall_factorsThrough_iff_mul φ E E' h
    u e₁ he₁ a₁ b₁ c₁ d₁ u' e₂ he₂ a₂ b₂ c₂ d₂

theorem isPullback_of_splits (hNℓ : N.Coprime ℓ) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S} {u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'}
    (h : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u')
    {E : FakeEllipticCurve Λ (N * ℓ) S} {E' : FakeEllipticCurve Λ (N * ℓ) S'} (h₁ : Splits u E) (h₂ : Splits u' E') :
    FakeEllipticCurve.IsPullback φ E E' := by
  obtain ⟨e₁, he₁, a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨e₂, he₂, a₂, b₂, c₂, d₂⟩ := h₂
  exact CerednikDrinfeld.QM.FakeEllipticCurve.isPullback_of_withExtraLevel_isPullback_of_forall_factorsThrough_iff_mul hNℓ φ u u' h
    E e₁ he₁ a₁ b₁ c₁ d₁ E' e₂ he₂ a₂ b₂ c₂ d₂

theorem isUnit_of_hom {B S : Type} [CommRing B] [CommRing S] (hu : IsUnit ((N * ℓ : ℕ) : B))
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) : IsUnit ((N * ℓ : ℕ) : S) := by
  obtain ⟨ψ, -⟩ := Spec.map_surjective s
  simpa using hu.map ψ.hom

end PairsLevel

open PairsLevel

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (hNℓ : N.Coprime ℓ)
    {B : Type} [CommRing B] (hu : IsUnit ((N * ℓ : ℕ) : B))
    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of B))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY)
    (hY : IsCoarseModuliT Λ N ℓ Y πY ptT) :
    ∃ pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
        FakeEllipticCurve Λ (N * ℓ) S → SchemeHomOver s πY,
      IsCoarseModuli Λ (N * ℓ) Y πY pt ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (E' : FakeEllipticCurve Λ (N * ℓ) S),
        (∃ (e : u.1.A ≅ E'.A) (he : e.hom ≫ E'.f = u.1.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
            mapPt e.hom he (u.1.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
          (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
            FactorsThrough u.1.lev P ↔
              FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t N (mapPt e.hom he P) = E'.L.one t) ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
            FactorsThrough u.2.levK P ↔
              FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t ℓ (mapPt e.hom he P) = E'.L.one t)) →
        pt S s E' = ptT S s u := by
  classical

  have hsplit : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E' : FakeEllipticCurve Λ (N * ℓ) S),
      ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S, Splits u E' := fun S _ s E' =>
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_forall_factorsThrough_iff_of_mul_of_isUnit Λ N ℓ hNℓ S
      (isUnit_of_hom (N := N) (ℓ := ℓ) hu s) E'
  have hcomb : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
      ∃ E' : FakeEllipticCurve Λ (N * ℓ) S, Splits u E' := fun S _ s u =>
    CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit Λ N ℓ hNℓ S
      (isUnit_of_hom (N := N) (ℓ := ℓ) hu s) u
  let split : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve Λ (N * ℓ) S → FakeEllipticCurve.WithExtraLevel Λ N ℓ S := fun S _ s E' => (hsplit S s E').choose
  have split_spec : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E' : FakeEllipticCurve Λ (N * ℓ) S),
      Splits (split S s E') E' := fun S _ s E' => (hsplit S s E').choose_spec
  let comb : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → FakeEllipticCurve Λ (N * ℓ) S := fun S _ s u => (hcomb S s u).choose
  have comb_spec : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
      Splits u (comb S s u) := fun S _ s u => (hcomb S s u).choose_spec

  let pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve Λ (N * ℓ) S → SchemeHomOver s πY := fun S _ s E' => ptT S s (split S s E')

  have hnorm : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (E' : FakeEllipticCurve Λ (N * ℓ) S), Splits u E' → pt S s E' = ptT S s u := by
    intro S _ s u E' h
    exact hY.ptT_iso S s _ _ (isoT_of_splits (iso_refl E') (split_spec S s E') h)
  refine ⟨pt, ⟨?_, ?_, ?_, ?_, ?_⟩, fun S _ s u E' h => hnorm S s u E' h⟩
  ·
    intro S _ s E E' h
    exact hY.ptT_iso S s _ _ (isoT_of_splits h (split_spec S s E) (split_spec S s E'))
  ·
    intro S S' _ _ φ s s' hs E E' h
    exact hY.ptT_pullback S S' φ s s' hs _ _ (isPullbackT_of_splits φ h (split_spec S s E) (split_spec S' s' E'))
  ·
    intro k _ _ s x
    obtain ⟨u, hu'⟩ := hY.ptT_surjective k s x
    refine ⟨comb k s u, ?_⟩
    rw [hnorm k s u (comb k s u) (comb_spec k s u), hu']
  ·
    intro k _ _ s E E' h
    exact iso_of_splits hNℓ (hY.ptT_injective k s _ _ h) (split_spec k s E) (split_spec k s E')
  ·
    intro T πT pt' hiso hbc

    let pt'T : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
        FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πT := fun S _ s u => pt' S s (comb S s u)
    have hisoT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → pt'T S s u = pt'T S s u' :=
      fun S _ s u u' h => hiso S s _ _ (iso_of_splits hNℓ h (comb_spec S s u) (comb_spec S s u'))
    have hbcT : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
        FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (pt'T S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt'T S s u).1 :=
      fun S S' _ _ φ s s' hs u u' h => hbc S S' φ s s' hs _ _ (isPullback_of_splits hNℓ φ h (comb_spec S s u) (comb_spec S' s' u'))
    obtain ⟨g, ⟨hgπ, hg⟩, huniq⟩ := hY.univ T πT pt'T hisoT hbcT
    refine ⟨g, ⟨hgπ, ?_⟩, ?_⟩
    · intro S _ s E'

      have h1 : pt' S s E' = pt'T S s (split S s E') :=
        hiso S s _ _ (iso_of_splits hNℓ (isoT_refl (split S s E')) (split_spec S s E') (comb_spec S s (split S s E')))
      rw [h1]
      exact hg S s (split S s E')
    · rintro g' ⟨hg'π, hg'⟩
      apply huniq
      refine ⟨hg'π, ?_⟩
      intro S _ s u

      rw [show pt'T S s u = pt' S s (comb S s u) from rfl, hg' S s (comb S s u), hnorm S s u (comb S s u) (comb_spec S s u)]

end S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_isCoarseModuli_mul_of_coprime_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_isCoarseModuli_mul_of_coprime_of_isUnit (solution)
