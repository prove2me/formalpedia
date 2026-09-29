-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/bf0caca2-f5bc-5d9c-a0bb-96573a710070

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

set_option maxHeartbeats 1600000

namespace B829Cp

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

theorem mapPt_inv_mul {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (e : A ≅ A') (he : e.hom ≫ f' = f) (he' : e.inv ≫ f = f')
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt e.hom he (L.mul t P Q) = L'.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f') :
    mapPt e.inv he' (L'.mul t P Q) = L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) := by
  have h := hmul t (mapPt e.inv he' P) (mapPt e.inv he' Q)
  rw [mapPt_hom_inv, mapPt_hom_inv] at h
  rw [← h, mapPt_inv_hom]

theorem nsmulPt_eq_pow {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t
    nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

def mapPtHom {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := L.pointGroup t; letI := L'.pointGroup t
    SchemeHomOver t f →* SchemeHomOver t f' := by
  letI := L.pointGroup t; letI := L'.pointGroup t
  exact { toFun := fun P => mapPt φ hφ P, map_one' := mapPt_one L L' φ hφ hmul t, map_mul' := fun P Q => hmul t P Q }

def levSubgroup {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {M : ℕ} (E : FakeEllipticCurve Λ M R)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := E.L.pointGroup t
    Subgroup (SchemeHomOver t E.f) := by
  letI := E.L.pointGroup t
  exact { carrier := {P | FactorsThrough E.lev P}
          mul_mem' := fun {P Q} hP hQ => (E.lev_sub t P Q hP hQ).1
          one_mem' := E.lev_one t
          inv_mem' := fun {P} hP => (E.lev_sub t P P hP hP).2 }

end B829Cp

namespace B829Cp

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem lev_transport {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} (hNℓ : N.Coprime ℓ) {S : Type} [CommRing S]
    (u₁ u₂ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (e : u₁.1.A ≅ u₂.1.A) (he : e.hom ≫ u₂.1.f = u₁.1.f)
    (e_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₁.1.f),
      mapPt e.hom he (u₁.1.L.mul t P Q) = u₂.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (e_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₁.1.f),
      FactorsThrough u₁.1.lev P → FactorsThrough u₂.1.lev (mapPt e.hom he P))
    (e_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₁.1.f),
      FactorsThrough u₁.2.levK P → FactorsThrough u₂.2.levK (mapPt e.hom he P))
    (E₁ : FakeEllipticCurve Λ (N * ℓ) S)
    (e₁ : u₁.1.A ≅ E₁.A) (he₁ : e₁.hom ≫ E₁.f = u₁.1.f)
    (e₁_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₁.1.f),
      mapPt e₁.hom he₁ (u₁.1.L.mul t P Q) = E₁.L.mul t (mapPt e₁.hom he₁ P) (mapPt e₁.hom he₁ Q))
    (e₁_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₁.1.f),
      FactorsThrough u₁.1.lev P ↔
        FactorsThrough E₁.lev (mapPt e₁.hom he₁ P) ∧ nsmulPt E₁.L t N (mapPt e₁.hom he₁ P) = E₁.L.one t)
    (e₁_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₁.1.f),
      FactorsThrough u₁.2.levK P ↔
        FactorsThrough E₁.lev (mapPt e₁.hom he₁ P) ∧ nsmulPt E₁.L t ℓ (mapPt e₁.hom he₁ P) = E₁.L.one t)
    (E₂ : FakeEllipticCurve Λ (N * ℓ) S)
    (e₂ : u₂.1.A ≅ E₂.A) (he₂ : e₂.hom ≫ E₂.f = u₂.1.f)
    (e₂_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₂.1.f),
      mapPt e₂.hom he₂ (u₂.1.L.mul t P Q) = E₂.L.mul t (mapPt e₂.hom he₂ P) (mapPt e₂.hom he₂ Q))
    (e₂_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₂.1.f),
      FactorsThrough u₂.1.lev P ↔
        FactorsThrough E₂.lev (mapPt e₂.hom he₂ P) ∧ nsmulPt E₂.L t N (mapPt e₂.hom he₂ P) = E₂.L.one t)
    (e₂_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₂.1.f),
      FactorsThrough u₂.2.levK P ↔
        FactorsThrough E₂.lev (mapPt e₂.hom he₂ P) ∧ nsmulPt E₂.L t ℓ (mapPt e₂.hom he₂ P) = E₂.L.one t)
    (he₁' : e₁.inv ≫ u₁.1.f = E₁.f) (hcomp : (e₁.inv ≫ e.hom ≫ e₂.hom) ≫ E₂.f = E₁.f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E₁.f) (hQ : FactorsThrough E₁.lev Q) :
    FactorsThrough E₂.lev (mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp Q) := by
  letI := E₁.L.pointGroup t
  letI := E₂.L.pointGroup t

  have hfac : ∀ X : SchemeHomOver t E₁.f,
      mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp X = mapPt e₂.hom he₂ (mapPt e.hom he (mapPt e₁.inv he₁' X)) := by
    intro X
    apply Subtype.ext
    simp only [mapPt_coe, Category.assoc]
  have Φmul : ∀ {T' : Scheme.{0}} (t' : T' ⟶ Spec (CommRingCat.of S)) (P P' : SchemeHomOver t' E₁.f),
      mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp (E₁.L.mul t' P P') =
        E₂.L.mul t' (mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp P) (mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp P') := by
    intro T' t' P P'
    have h1 : ∀ X : SchemeHomOver t' E₁.f,
        mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp X = mapPt e₂.hom he₂ (mapPt e.hom he (mapPt e₁.inv he₁' X)) := by
      intro X; apply Subtype.ext; simp only [mapPt_coe, Category.assoc]
    rw [h1, h1, h1, mapPt_inv_mul u₁.1.L E₁.L e₁ he₁ he₁' e₁_hom, e_hom, e₂_hom]
  let Φ := mapPtHom E₁.L E₂.L (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp Φmul t
  have hΦ : ∀ X : SchemeHomOver t E₁.f, Φ X = mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp X := fun X => rfl

  obtain ⟨α, β, hαβ⟩ : IsCoprime (N : ℤ) (ℓ : ℤ) := Nat.isCoprime_iff_coprime.2 hNℓ

  have hQtor : Q ^ (N * ℓ) = 1 := by
    rw [← nsmulPt_eq_pow]; exact E₁.lev_torsion t Q hQ

  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : SchemeHomOver t E₁.f, Q₁ = Q ^ (β * (ℓ : ℤ)) := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : SchemeHomOver t E₁.f, Q₂ = Q ^ (α * (N : ℤ)) := ⟨_, rfl⟩
  have hsplit : Q = Q₁ * Q₂ := by
    rw [hQ₁, hQ₂, ← zpow_add]
    have h1 : β * (ℓ : ℤ) + α * (N : ℤ) = 1 := by linarith [hαβ]
    rw [h1, zpow_one]
  have hQmem : Q ∈ levSubgroup E₁ t := hQ
  have hQ₁mem : FactorsThrough E₁.lev Q₁ := by
    have h := (levSubgroup E₁ t).zpow_mem hQmem (β * (ℓ : ℤ)); rw [← hQ₁] at h; exact h
  have hQ₂mem : FactorsThrough E₁.lev Q₂ := by
    have h := (levSubgroup E₁ t).zpow_mem hQmem (α * (N : ℤ)); rw [← hQ₂] at h; exact h
  have hQ₁tor : nsmulPt E₁.L t N Q₁ = E₁.L.one t := by
    rw [nsmulPt_eq_pow]
    show Q₁ ^ N = 1
    rw [hQ₁, ← zpow_natCast, ← zpow_mul]
    have h1 : β * (ℓ : ℤ) * (N : ℤ) = ((N * ℓ : ℕ) : ℤ) * β := by push_cast; ring
    rw [h1, zpow_mul, zpow_natCast, hQtor, one_zpow]
  have hQ₂tor : nsmulPt E₁.L t ℓ Q₂ = E₁.L.one t := by
    rw [nsmulPt_eq_pow]
    show Q₂ ^ ℓ = 1
    rw [hQ₂, ← zpow_natCast, ← zpow_mul]
    have h1 : α * (N : ℤ) * (ℓ : ℤ) = ((N * ℓ : ℕ) : ℤ) * α := by push_cast; ring
    rw [h1, zpow_mul, zpow_natCast, hQtor, one_zpow]

  have h1 : FactorsThrough u₁.1.lev (mapPt e₁.inv he₁' Q₁) :=
    (e₁_lev t _).2 (by rw [mapPt_hom_inv]; exact ⟨hQ₁mem, hQ₁tor⟩)
  have h3 := ((e₂_lev t _).1 (e_lev t _ h1)).1
  rw [← hfac] at h3
  have k1 : FactorsThrough u₁.2.levK (mapPt e₁.inv he₁' Q₂) :=
    (e₁_levK t _).2 (by rw [mapPt_hom_inv]; exact ⟨hQ₂mem, hQ₂tor⟩)
  have k3 := ((e₂_levK t _).1 (e_levK t _ k1)).1
  rw [← hfac] at k3

  rw [hsplit]
  show FactorsThrough E₂.lev (mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp (E₁.L.mul t Q₁ Q₂))
  rw [Φmul]
  exact (E₂.lev_sub t _ _ h3 k3).1

end B829Cp

open B829Cp in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} (hNℓ : N.Coprime ℓ) {S : Type} [CommRing S]
    (u₁ u₂ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (h : FakeEllipticCurve.WithExtraLevel.Iso u₁ u₂)
    (E₁ : FakeEllipticCurve Λ (N * ℓ) S)
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
    (E₂ : FakeEllipticCurve Λ (N * ℓ) S)
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
    FakeEllipticCurve.Iso E₁ E₂ := by
  obtain ⟨e, he, e_hom, e_act, e_lev, e_levK⟩ := h
  have he' : e.inv ≫ u₁.1.f = u₂.1.f := by rw [← he, Iso.inv_hom_id_assoc]
  have he₁' : e₁.inv ≫ u₁.1.f = E₁.f := by rw [← he₁, Iso.inv_hom_id_assoc]
  have he₂' : e₂.inv ≫ u₂.1.f = E₂.f := by rw [← he₂, Iso.inv_hom_id_assoc]
  have hcomp : (e₁.inv ≫ e.hom ≫ e₂.hom) ≫ E₂.f = E₁.f := by simp only [Category.assoc, he₂, he, he₁']
  have hcomp' : (e₂.inv ≫ e.inv ≫ e₁.hom) ≫ E₁.f = E₂.f := by simp only [Category.assoc, he₁, he', he₂']

  have e_hom' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₂.1.f),
      mapPt e.inv he' (u₂.1.L.mul t P Q) = u₁.1.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) :=
    mapPt_inv_mul u₁.1.L u₂.1.L e he he' e_hom
  have e_lev' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₂.1.f),
      FactorsThrough u₂.1.lev P → FactorsThrough u₁.1.lev (mapPt e.inv he' P) := by
    intro T t P hP
    apply (e_lev t (mapPt e.inv he' P)).2
    rw [mapPt_hom_inv]; exact hP
  have e_levK' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₂.1.f),
      FactorsThrough u₂.2.levK P → FactorsThrough u₁.2.levK (mapPt e.inv he' P) := by
    intro T t P hP
    apply (e_levK t (mapPt e.inv he' P)).2
    rw [mapPt_hom_inv]; exact hP

  have hE : (e₁.symm ≪≫ e ≪≫ e₂).hom ≫ E₂.f = E₁.f := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, he₂, he, he₁']
  have hf : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (X : SchemeHomOver t E₁.f),
      mapPt (e₁.symm ≪≫ e ≪≫ e₂).hom hE X = mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp X := by
    intro T t X; apply Subtype.ext; simp only [mapPt_coe, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hf3 : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (X : SchemeHomOver t E₁.f),
      mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp X = mapPt e₂.hom he₂ (mapPt e.hom he (mapPt e₁.inv he₁' X)) := by
    intro T t X; apply Subtype.ext; simp only [mapPt_coe, Category.assoc]
  have hback : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (X : SchemeHomOver t E₁.f),
      mapPt (e₂.inv ≫ e.inv ≫ e₁.hom) hcomp' (mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp X) = X := by
    intro T t X; apply Subtype.ext
    simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Iso.inv_hom_id, Category.comp_id]
  refine ⟨e₁.symm ≪≫ e ≪≫ e₂, hE, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    rw [hf, hf, hf, hf3, hf3, hf3, mapPt_inv_mul u₁.1.L E₁.L e₁ he₁ he₁' e₁_hom, e_hom, e₂_hom]
  ·
    intro x
    have h1 : E₁.act x ≫ e₁.inv = e₁.inv ≫ u₁.1.act x := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, e₁_act x]
    show E₁.act x ≫ (e₁.inv ≫ e.hom ≫ e₂.hom) = (e₁.inv ≫ e.hom ≫ e₂.hom) ≫ E₂.act x
    calc E₁.act x ≫ (e₁.inv ≫ e.hom ≫ e₂.hom)
        = (E₁.act x ≫ e₁.inv) ≫ e.hom ≫ e₂.hom := by simp only [Category.assoc]
      _ = e₁.inv ≫ (u₁.1.act x ≫ e.hom) ≫ e₂.hom := by rw [h1]; simp only [Category.assoc]
      _ = e₁.inv ≫ e.hom ≫ (u₂.1.act x ≫ e₂.hom) := by rw [e_act]; simp only [Category.assoc]
      _ = (e₁.inv ≫ e.hom ≫ e₂.hom) ≫ E₂.act x := by rw [e₂_act]; simp only [Category.assoc]
  ·
    intro T t Q
    rw [hf]
    constructor
    · intro hQ
      exact lev_transport hNℓ u₁ u₂ e he e_hom (fun t P hP => (e_lev t P).1 hP) (fun t P hP => (e_levK t P).1 hP)
        E₁ e₁ he₁ e₁_hom e₁_lev e₁_levK E₂ e₂ he₂ e₂_hom e₂_lev e₂_levK he₁' hcomp t Q hQ
    · intro hQ'
      have h : FactorsThrough E₁.lev
          (mapPt (e₂.inv ≫ e.inv ≫ e₁.hom) hcomp' (mapPt (e₁.inv ≫ e.hom ≫ e₂.hom) hcomp Q)) :=
        lev_transport hNℓ u₂ u₁ e.symm he' e_hom' e_lev' e_levK'
          E₂ e₂ he₂ e₂_hom e₂_lev e₂_levK E₁ e₁ he₁ e₁_hom e₁_lev e₁_levK he₂' hcomp' t _ hQ'
      rw [hback] at h
      exact h

end S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul (solution)
