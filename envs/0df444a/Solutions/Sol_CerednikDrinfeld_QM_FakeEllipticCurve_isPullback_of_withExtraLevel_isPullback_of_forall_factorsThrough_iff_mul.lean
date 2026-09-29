-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isPullback_of_withExtraLevel_isPullback_of_forall_factorsThrough_iff_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/107224a4-b909-5bb3-b31d-471b84435e24

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_withExtraLevel_isPullback_of_forall_factorsThrough_iff_mul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

set_option maxHeartbeats 1600000

namespace B829Dp

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

variable {R : Type} [CommRing R]

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

def levSubgroup {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {M : ℕ} (E : FakeEllipticCurve Λ M R)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := E.L.pointGroup t
    Subgroup (SchemeHomOver t E.f) := by
  letI := E.L.pointGroup t
  exact { carrier := {P | FactorsThrough E.lev P}
          mul_mem' := fun {P Q} hP hQ => (E.lev_sub t P Q hP hQ).1
          one_mem' := E.lev_one t
          inv_mem' := fun {P} hP => (E.lev_sub t P P hP hP).2 }

theorem exists_mul_of_coprime {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} (hNℓ : N.Coprime ℓ)
    (E : FakeEllipticCurve Λ (N * ℓ) R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (Q : SchemeHomOver t E.f) (hQ : FactorsThrough E.lev Q) :
    ∃ Q₁ Q₂ : SchemeHomOver t E.f, Q = E.L.mul t Q₁ Q₂ ∧
      FactorsThrough E.lev Q₁ ∧ nsmulPt E.L t N Q₁ = E.L.one t ∧
      FactorsThrough E.lev Q₂ ∧ nsmulPt E.L t ℓ Q₂ = E.L.one t := by
  letI := E.L.pointGroup t
  obtain ⟨α, β, hαβ⟩ : IsCoprime (N : ℤ) (ℓ : ℤ) := Nat.isCoprime_iff_coprime.2 hNℓ
  have hQtor : Q ^ (N * ℓ) = 1 := by
    rw [← nsmulPt_eq_pow]; exact E.lev_torsion t Q hQ
  have hQmem : Q ∈ levSubgroup E t := hQ
  refine ⟨Q ^ (β * (ℓ : ℤ)), Q ^ (α * (N : ℤ)), ?_, ?_, ?_, ?_, ?_⟩
  · show Q = Q ^ (β * (ℓ : ℤ)) * Q ^ (α * (N : ℤ))
    rw [← zpow_add]
    have h1 : β * (ℓ : ℤ) + α * (N : ℤ) = 1 := by linarith [hαβ]
    rw [h1, zpow_one]
  · exact (levSubgroup E t).zpow_mem hQmem (β * (ℓ : ℤ))
  · rw [nsmulPt_eq_pow]
    show (Q ^ (β * (ℓ : ℤ))) ^ N = 1
    rw [← zpow_natCast, ← zpow_mul]
    have h1 : β * (ℓ : ℤ) * (N : ℤ) = ((N * ℓ : ℕ) : ℤ) * β := by push_cast; ring
    rw [h1, zpow_mul, zpow_natCast, hQtor, one_zpow]
  · exact (levSubgroup E t).zpow_mem hQmem (α * (N : ℤ))
  · rw [nsmulPt_eq_pow]
    show (Q ^ (α * (N : ℤ))) ^ ℓ = 1
    rw [← zpow_natCast, ← zpow_mul]
    have h1 : α * (N : ℤ) * (ℓ : ℤ) = ((N * ℓ : ℕ) : ℤ) * α := by push_cast; ring
    rw [h1, zpow_mul, zpow_natCast, hQtor, one_zpow]

end B829Dp

open B829Dp in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} (hNℓ : N.Coprime ℓ) {S S' : Type} [CommRing S] [CommRing S']
    (φ : S →+* S')
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (h : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u')
    (E : FakeEllipticCurve Λ (N * ℓ) S)
    (e : u.1.A ≅ E.A) (he : e.hom ≫ E.f = u.1.f)
    (e_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (e_act : ∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E.act x)
    (e_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔
        FactorsThrough E.lev (mapPt e.hom he P) ∧ nsmulPt E.L t N (mapPt e.hom he P) = E.L.one t)
    (e_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P ↔
        FactorsThrough E.lev (mapPt e.hom he P) ∧ nsmulPt E.L t ℓ (mapPt e.hom he P) = E.L.one t)
    (E' : FakeEllipticCurve Λ (N * ℓ) S')
    (e' : u'.1.A ≅ E'.A) (he' : e'.hom ≫ E'.f = u'.1.f)
    (e'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t u'.1.f),
      mapPt e'.hom he' (u'.1.L.mul t P Q) = E'.L.mul t (mapPt e'.hom he' P) (mapPt e'.hom he' Q))
    (e'_act : ∀ x : ↥Λ, u'.1.act x ≫ e'.hom = e'.hom ≫ E'.act x)
    (e'_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t u'.1.f),
      FactorsThrough u'.1.lev P ↔
        FactorsThrough E'.lev (mapPt e'.hom he' P) ∧ nsmulPt E'.L t N (mapPt e'.hom he' P) = E'.L.one t)
    (e'_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t u'.1.f),
      FactorsThrough u'.2.levK P ↔
        FactorsThrough E'.lev (mapPt e'.hom he' P) ∧ nsmulPt E'.L t ℓ (mapPt e'.hom he' P) = E'.L.one t) :
    FakeEllipticCurve.IsPullback φ E E' := by
  obtain ⟨g, hg, h_hom, h_act, h_lev⟩ := h
  have he₀ : e.inv ≫ u.1.f = E.f := by rw [← he, Iso.inv_hom_id_assoc]
  have he₀' : e'.inv ≫ u'.1.f = E'.f := by rw [← he', Iso.inv_hom_id_assoc]

  let g' : E'.A ⟶ E.A := e'.inv ≫ g ≫ e.hom
  have hg' : CategoryTheory.IsPullback g' E'.f E.f (Spec.map (CommRingCat.ofHom φ)) := by
    refine hg.of_iso e' e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [g', Iso.hom_inv_id_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, he']
    · simp only [Iso.refl_hom, Category.comp_id, he]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

  let G : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')),
      SchemeHomOver t' u'.1.f → SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) u.1.f :=
    fun t' P => ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
  have hG : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' u'.1.f),
      G t' (u'.1.L.mul t' P Q) = u.1.L.mul _ (G t' P) (G t' Q) := by
    intro T t' P Q
    apply Subtype.ext
    exact h_hom t' P Q

  have hkey : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      (⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩ :
          SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f) =
        mapPt e.hom he (G t' (mapPt e'.inv he₀' P)) := by
    intro T t' P
    apply Subtype.ext
    simp only [g', G, mapPt_coe, Category.assoc]
  refine ⟨g', hg', ?_, ?_, ?_⟩
  ·
    intro T t' P Q
    have h1 := hkey t' (E'.L.mul t' P Q)
    have h2 := hkey t' P
    have h3 := hkey t' Q
    rw [mapPt_inv_mul u'.1.L E'.L e' he' he₀' e'_hom, hG, e_hom] at h1
    rw [← h2, ← h3] at h1
    exact congrArg Subtype.val h1
  ·
    intro x
    have h2 : E'.act x ≫ e'.inv = e'.inv ≫ u'.1.act x := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, e'_act x]
    show E'.act x ≫ (e'.inv ≫ g ≫ e.hom) = (e'.inv ≫ g ≫ e.hom) ≫ E.act x
    calc E'.act x ≫ (e'.inv ≫ g ≫ e.hom)
        = (E'.act x ≫ e'.inv) ≫ g ≫ e.hom := by simp only [Category.assoc]
      _ = e'.inv ≫ (u'.1.act x ≫ g) ≫ e.hom := by rw [h2]; simp only [Category.assoc]
      _ = e'.inv ≫ g ≫ (u.1.act x ≫ e.hom) := by rw [h_act]; simp only [Category.assoc]
      _ = (e'.inv ≫ g ≫ e.hom) ≫ E.act x := by rw [e_act]; simp only [Category.assoc]
  ·
    intro T t' P hP
    obtain ⟨P₁, P₂, hP12, hP₁, hP₁t, hP₂, hP₂t⟩ := exists_mul_of_coprime hNℓ E' t' P hP

    have h1 : FactorsThrough u'.1.lev (mapPt e'.inv he₀' P₁) :=
      (e'_lev t' _).2 (by rw [mapPt_hom_inv]; exact ⟨hP₁, hP₁t⟩)
    obtain ⟨P₀, hP₀⟩ := (h_lev t' (mapPt e'.inv he₀' P₁)).1 h1
    have h1' : FactorsThrough u.1.lev (G t' (mapPt e'.inv he₀' P₁)) := ⟨P₀, hP₀⟩
    have h1'' := ((e_lev _ _).1 h1').1

    have h2 : FactorsThrough u'.2.levK (mapPt e'.inv he₀' P₂) :=
      (e'_levK t' _).2 (by rw [mapPt_hom_inv]; exact ⟨hP₂, hP₂t⟩)
    obtain ⟨R₀, hR₀⟩ := (h_lev t' (mapPt e'.inv he₀' P₂)).2 h2
    have h2' : FactorsThrough u.2.levK (G t' (mapPt e'.inv he₀' P₂)) := ⟨R₀, hR₀⟩
    have h2'' := ((e_levK _ _).1 h2').1

    have hprod := (E.lev_sub _ _ _ h1'' h2'').1
    rw [← e_hom, ← hG, ← mapPt_inv_mul u'.1.L E'.L e' he' he₀' e'_hom, ← hP12, ← hkey] at hprod
    exact hprod

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_withExtraLevel_isPullback_of_forall_factorsThrough_iff_mul
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_withExtraLevel_isPullback_of_forall_factorsThrough_iff_mul (solution)
