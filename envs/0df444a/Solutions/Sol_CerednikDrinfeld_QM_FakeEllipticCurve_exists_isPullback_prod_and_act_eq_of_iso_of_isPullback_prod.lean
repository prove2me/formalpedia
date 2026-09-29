-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_prod_and_act_eq_of_iso_of_isPullback_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/3a405560-164b-55bc-9b96-d40fd4ff3076

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_prod_and_act_eq_of_iso_of_isPullback_prod

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace Transport91

universe u

theorem mapPt_comp {R : Type u} [CommRing R] {A A' A'' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f') {h : (φ ≫ ψ) ≫ f'' = f}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (Category.assoc _ _ _).symm

end Transport91

theorem solution
    {M N : ℕ} (S : Type) [CommRing S]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (E₁ : FakeEllipticCurve Λ M S) (A₀ : FakeEllipticCurve Λ N S)

    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (p₁ p₂ : E₁.A ⟶ A) (hp₁ : p₁ ≫ f = E₁.f) (hp₂ : p₂ ≫ f = E₁.f) (hpb : CategoryTheory.IsPullback p₁ p₂ f f)
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E₁.f),
      mapPt p₁ hp₁ (E₁.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
      mapPt p₂ hp₂ (E₁.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q))
    (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (E₁.A ⟶ E₁.A))
    (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ E₁.f = E₁.f)
    (hE_mat : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E₁.f),
      mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
      mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P)))
    (hact : ∀ m : ↥Λ, E₁.act m = E (j (m : ℍ[ℚ, a, b])) (hj m))
    (hE_hom : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E₁.f),
      pushPt (E y hy) (hE y hy) (E₁.L.mul t P Q) = E₁.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q))
    (hE_one : ∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 E₁.A)
    (hE_mul : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy)
    (hE_add : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E₁.f),
      pushPt (E (y + y') hyy') (hE _ hyy') P = E₁.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P))

    (u : A₀.A ⟶ E₁.A) (u' : E₁.A ⟶ A₀.A) (hu : u ≫ E₁.f = A₀.f)
    (huu' : u ≫ u' = 𝟙 A₀.A) (hu'u : u' ≫ u = 𝟙 E₁.A)
    (hu_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
      mapPt u hu (A₀.L.mul t P Q) = E₁.L.mul t (mapPt u hu P) (mapPt u hu Q))
    (hu_act : ∀ x : ↥Λ, A₀.act x ≫ u = u ≫ E₁.act x) :
    ∃ (p₁ p₂ : A₀.A ⟶ A) (hp₁ : p₁ ≫ f = A₀.f) (hp₂ : p₂ ≫ f = A₀.f)
      (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (A₀.A ⟶ A₀.A))
      (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ A₀.f = A₀.f),

      CategoryTheory.IsPullback p₁ p₂ f f ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
        mapPt p₁ hp₁ (A₀.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
        mapPt p₂ hp₂ (A₀.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q)) ∧

      (∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
          {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
        mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
          L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
        mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
          L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P))) ∧

      (∀ m : ↥Λ, A₀.act m = E (j (m : ℍ[ℚ, a, b])) (hj m)) ∧

      (∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
          {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
        pushPt (E y hy) (hE y hy) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q)) ∧
      (∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 A₀.A) ∧
      (∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
          (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy) ∧
      (∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
          (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
        pushPt (E (y + y') hyy') (hE _ hyy') P = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P)) := by

  have hu'o : u' ≫ A₀.f = E₁.f := by rw [← hu, ← Category.assoc, hu'u, Category.id_comp]
  have hu'u' : ∀ {Z : Scheme.{0}} (h : E₁.A ⟶ Z), u' ≫ u ≫ h = h := fun h => by
    rw [← Category.assoc, hu'u, Category.id_comp]
  have huu'' : ∀ {Z : Scheme.{0}} (h : A₀.A ⟶ Z), u ≫ u' ≫ h = h := fun h => by
    rw [← Category.assoc, huu', Category.id_comp]
  have cancel₁ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (X : SchemeHomOver t A₀.f),
      mapPt u' hu'o (mapPt u hu X) = X := fun X =>
    Subtype.ext (by simp only [mapPt_coe, Category.assoc, huu', Category.comp_id])
  have cancel₂ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (X : SchemeHomOver t E₁.f),
      mapPt u hu (mapPt u' hu'o X) = X := fun X =>
    Subtype.ext (by simp only [mapPt_coe, Category.assoc, hu'u, Category.comp_id])

  have hu'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E₁.f),
      mapPt u' hu'o (E₁.L.mul t P Q) = A₀.L.mul t (mapPt u' hu'o P) (mapPt u' hu'o Q) := by
    intro T t P Q
    have h := hu_hom t (mapPt u' hu'o P) (mapPt u' hu'o Q)
    rw [cancel₂, cancel₂] at h
    rw [← h, cancel₁]

  have hp₁' : (u ≫ p₁) ≫ f = A₀.f := by rw [Category.assoc, hp₁, hu]
  have hp₂' : (u ≫ p₂) ≫ f = A₀.f := by rw [Category.assoc, hp₂, hu]
  have hE' : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), (u ≫ E y hy ≫ u') ≫ A₀.f = A₀.f := by
    intro y hy; simp only [Category.assoc]; rw [hu'o, hE, hu]

  have conj : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
      {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (X : SchemeHomOver t A₀.f),
      pushPt (u ≫ E y hy ≫ u') (hE' y hy) X = mapPt u' hu'o (pushPt (E y hy) (hE y hy) (mapPt u hu X)) :=
    fun y hy {T} {t} X => Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  refine ⟨u ≫ p₁, u ≫ p₂, hp₁', hp₂', fun y hy => u ≫ E y hy ≫ u', hE', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact hpb.of_iso' ⟨u, u', huu', hu'u⟩ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  ·
    intro T t P Q
    obtain ⟨h1, h2⟩ := hp_hom t (mapPt u hu P) (mapPt u hu Q)
    refine ⟨?_, ?_⟩
    · rw [Transport91.mapPt_comp u hu p₁ hp₁, Transport91.mapPt_comp u hu p₁ hp₁,
        Transport91.mapPt_comp u hu p₁ hp₁, hu_hom, h1]
    · rw [Transport91.mapPt_comp u hu p₂ hp₂, Transport91.mapPt_comp u hu p₂ hp₂,
        Transport91.mapPt_comp u hu p₂ hp₂, hu_hom, h2]
  ·
    intro y hy T t P
    obtain ⟨m1, m2⟩ := hE_mat y hy t (mapPt u hu P)
    refine ⟨?_, ?_⟩
    · rw [Transport91.mapPt_comp u hu p₁ hp₁, Transport91.mapPt_comp u hu p₁ hp₁,
        Transport91.mapPt_comp u hu p₂ hp₂, ← m1]
      exact Subtype.ext (by simp only [mapPt_coe, Category.assoc, hu'u'])
    · rw [Transport91.mapPt_comp u hu p₂ hp₂, Transport91.mapPt_comp u hu p₁ hp₁,
        Transport91.mapPt_comp u hu p₂ hp₂, ← m2]
      exact Subtype.ext (by simp only [mapPt_coe, Category.assoc, hu'u'])
  ·
    intro m
    show A₀.act m = u ≫ E (j (m : ℍ[ℚ, a, b])) (hj m) ≫ u'
    rw [← hact m, ← Category.assoc, ← hu_act m, Category.assoc, huu', Category.comp_id]
  ·
    intro y hy T t P Q
    rw [conj, conj, conj, hu_hom, hE_hom, hu'_hom]
  ·
    intro h1
    show u ≫ E 1 h1 ≫ u' = 𝟙 A₀.A
    rw [hE_one h1, Category.id_comp, huu']
  ·
    intro y y' hy hy' hyy'
    show u ≫ E (y * y') hyy' ≫ u' = (u ≫ E y' hy' ≫ u') ≫ (u ≫ E y hy ≫ u')
    rw [hE_mul y y' hy hy' hyy']
    simp only [Category.assoc, hu'u']
  ·
    intro y y' hy hy' hyy' T t P
    rw [conj, conj, conj, hE_add y y' hy hy' hyy', hu'_hom]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_prod_and_act_eq_of_iso_of_isPullback_prod
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_prod_and_act_eq_of_iso_of_isPullback_prod (solution)
