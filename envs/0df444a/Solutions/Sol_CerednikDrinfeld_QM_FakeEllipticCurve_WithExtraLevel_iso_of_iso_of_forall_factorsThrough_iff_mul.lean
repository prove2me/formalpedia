-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_iso_of_forall_factorsThrough_iff_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/29385eaf-6072-50b5-a848-a1f494b81096

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_iso_of_forall_factorsThrough_iff_mul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

set_option maxHeartbeats 1600000

namespace B829C

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

variable {R : Type} [CommRing R]

theorem mapPt_mapPt {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f)
    (hφψ : (φ ≫ ψ) ≫ f'' = f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) hφψ P := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]

theorem mapPt_hom_inv {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (e : A ≅ A') (he : e.hom ≫ f' = f) (he' : e.inv ≫ f = f')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f') :
    mapPt e.hom he (mapPt e.inv he' P) = P := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem mapPt_inv_hom {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (e : A ≅ A') (he : e.hom ≫ f' = f) (he' : e.inv ≫ f = f')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt e.inv he' (mapPt e.hom he P) = P := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem mapPt_one {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  set a := mapPt φ hφ (L.one t) with ha
  have h2 : L'.mul t a a = a := by rw [ha, ← hmul, L.one_mul]
  calc a = L'.mul t (L'.one t) a := (L'.one_mul t a).symm
    _ = L'.mul t (L'.mul t (L'.inv t a) a) a := by rw [L'.inv_mul_cancel]
    _ = L'.mul t (L'.inv t a) (L'.mul t a a) := by rw [L'.mul_assoc]
    _ = L'.mul t (L'.inv t a) a := by rw [h2]
    _ = L'.one t := L'.inv_mul_cancel t a

theorem mapPt_nsmulPt {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one L L' φ hφ hmul t
  | succ n ih => simp only [nsmulPt, hmul, ih]

theorem mapPt_inv_mul {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (e : A ≅ A') (he : e.hom ≫ f' = f) (he' : e.inv ≫ f = f')
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt e.hom he (L.mul t P Q) = L'.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f') :
    mapPt e.inv he' (L'.mul t P Q) = L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) := by
  have h := hmul t (mapPt e.inv he' P) (mapPt e.inv he' Q)
  rw [mapPt_hom_inv, mapPt_hom_inv] at h
  rw [← h, mapPt_inv_hom]

theorem nsmulPt_eq_one_iff {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (e : A ≅ A') (he : e.hom ≫ f' = f) (he' : e.inv ≫ f = f')
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt e.hom he (L.mul t P Q) = L'.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.one t ↔ nsmulPt L' t n (mapPt e.hom he P) = L'.one t := by
  constructor
  · intro h
    rw [← mapPt_nsmulPt L L' e.hom he hmul, h, mapPt_one L L' e.hom he hmul]
  · intro h
    have h2 := congrArg (mapPt e.inv he') h
    rw [← mapPt_nsmulPt L L' e.hom he hmul, mapPt_inv_hom,
      mapPt_one L' L e.inv he' (mapPt_inv_mul L L' e he he' hmul)] at h2
    exact h2

end B829C

open B829C in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S : Type} [CommRing S]
    (E₁ E₂ : FakeEllipticCurve Λ (N * ℓ) S) (h : FakeEllipticCurve.Iso E₁ E₂)
    (u₁ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (e₁ : u₁.1.A ≅ E₁.A) (he₁ : e₁.hom ≫ E₁.f = u₁.1.f)
    (e₁_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₁.1.f),
      mapPt e₁.hom he₁ (u₁.1.L.mul t P Q) = E₁.L.mul t (mapPt e₁.hom he₁ P) (mapPt e₁.hom he₁ Q))
    (e₁_act : ∀ x : ↥Λ, u₁.1.act x ≫ e₁.hom = e₁.hom ≫ E₁.act x)
    (e₁_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₁.1.f),
      FactorsThrough u₁.1.lev P ↔
        FactorsThrough E₁.lev (mapPt e₁.hom he₁ P) ∧ nsmulPt E₁.L t N (mapPt e₁.hom he₁ P) = E₁.L.one t)
    (e₁_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₁.1.f),
      FactorsThrough u₁.2.levK P ↔
        FactorsThrough E₁.lev (mapPt e₁.hom he₁ P) ∧ nsmulPt E₁.L t ℓ (mapPt e₁.hom he₁ P) = E₁.L.one t)
    (u₂ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (e₂ : u₂.1.A ≅ E₂.A) (he₂ : e₂.hom ≫ E₂.f = u₂.1.f)
    (e₂_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₂.1.f),
      mapPt e₂.hom he₂ (u₂.1.L.mul t P Q) = E₂.L.mul t (mapPt e₂.hom he₂ P) (mapPt e₂.hom he₂ Q))
    (e₂_act : ∀ x : ↥Λ, u₂.1.act x ≫ e₂.hom = e₂.hom ≫ E₂.act x)
    (e₂_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₂.1.f),
      FactorsThrough u₂.1.lev P ↔
        FactorsThrough E₂.lev (mapPt e₂.hom he₂ P) ∧ nsmulPt E₂.L t N (mapPt e₂.hom he₂ P) = E₂.L.one t)
    (e₂_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₂.1.f),
      FactorsThrough u₂.2.levK P ↔
        FactorsThrough E₂.lev (mapPt e₂.hom he₂ P) ∧ nsmulPt E₂.L t ℓ (mapPt e₂.hom he₂ P) = E₂.L.one t) :
    FakeEllipticCurve.WithExtraLevel.Iso u₁ u₂ := by
  obtain ⟨e₁₂, he₁₂, h_hom, h_act, h_lev⟩ := h
  have he₁' : e₁.inv ≫ u₁.1.f = E₁.f := by rw [← he₁, Iso.inv_hom_id_assoc]
  have he₂' : e₂.inv ≫ u₂.1.f = E₂.f := by rw [← he₂, Iso.inv_hom_id_assoc]
  have he₁₂' : e₁₂.inv ≫ E₁.f = E₂.f := by rw [← he₁₂, Iso.inv_hom_id_assoc]
  have he : (e₁ ≪≫ e₁₂ ≪≫ e₂.symm).hom ≫ u₂.1.f = u₁.1.f := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, he₂', he₁₂, he₁]

  have hf : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (X : SchemeHomOver t u₁.1.f),
      mapPt (e₁ ≪≫ e₁₂ ≪≫ e₂.symm).hom he X = mapPt e₂.inv he₂' (mapPt e₁₂.hom he₁₂ (mapPt e₁.hom he₁ X)) := by
    intro T t X
    apply Subtype.ext
    simp only [mapPt_coe, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hf2 : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (X : SchemeHomOver t u₁.1.f),
      mapPt e₂.hom he₂ (mapPt (e₁ ≪≫ e₁₂ ≪≫ e₂.symm).hom he X) = mapPt e₁₂.hom he₁₂ (mapPt e₁.hom he₁ X) := by
    intro T t X
    rw [hf, mapPt_hom_inv]
  refine ⟨e₁ ≪≫ e₁₂ ≪≫ e₂.symm, he, ?_, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    rw [hf, hf, hf, e₁_hom, h_hom, mapPt_inv_mul u₂.1.L E₂.L e₂ he₂ he₂' e₂_hom]
  ·
    intro x
    have h2 : E₂.act x ≫ e₂.inv = e₂.inv ≫ u₂.1.act x := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, e₂_act x]
    show u₁.1.act x ≫ (e₁.hom ≫ e₁₂.hom ≫ e₂.inv) = (e₁.hom ≫ e₁₂.hom ≫ e₂.inv) ≫ u₂.1.act x
    calc u₁.1.act x ≫ (e₁.hom ≫ e₁₂.hom ≫ e₂.inv)
        = (u₁.1.act x ≫ e₁.hom) ≫ e₁₂.hom ≫ e₂.inv := by simp only [Category.assoc]
      _ = e₁.hom ≫ (E₁.act x ≫ e₁₂.hom) ≫ e₂.inv := by rw [e₁_act]; simp only [Category.assoc]
      _ = e₁.hom ≫ e₁₂.hom ≫ (E₂.act x ≫ e₂.inv) := by rw [h_act]; simp only [Category.assoc]
      _ = (e₁.hom ≫ e₁₂.hom ≫ e₂.inv) ≫ u₂.1.act x := by rw [h2]; simp only [Category.assoc]
  ·
    intro T t P
    rw [e₁_lev, e₂_lev, hf2, h_lev t (mapPt e₁.hom he₁ P),
      nsmulPt_eq_one_iff E₁.L E₂.L e₁₂ he₁₂ he₁₂' h_hom t N (mapPt e₁.hom he₁ P)]
  ·
    intro T t P
    rw [e₁_levK, e₂_levK, hf2, h_lev t (mapPt e₁.hom he₁ P),
      nsmulPt_eq_one_iff E₁.L E₂.L e₁₂ he₁₂ he₁₂' h_hom t ℓ (mapPt e₁.hom he₁ P)]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_iso_of_forall_factorsThrough_iff_mul
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_iso_of_forall_factorsThrough_iff_mul (solution)
