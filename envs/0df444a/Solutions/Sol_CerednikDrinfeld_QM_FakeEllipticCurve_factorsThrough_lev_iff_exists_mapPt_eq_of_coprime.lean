-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c279c6e5-d92b-513c-991e-a9fb90fc8cae

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace LevelOnto

variable {S : Type u} [CommRing S]

section Pow

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

theorem nsmulPt_eq_pow (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t
    nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
    show L.mul t (nsmulPt L t n P) P = P ^ (n + 1)
    rw [ih, pow_succ]; rfl

theorem nsmulPt_one' (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  letI := L.pointGroup t
  rw [nsmulPt_eq_pow]; exact one_pow n

end Pow

end LevelOnto

open LevelOnto in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f) (n : ℕ) (hn : Nat.Coprime n N)
    (hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t n P)
    (hlev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E'.f),
      FactorsThrough E'.lev Q ↔ ∃ P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt φ hφ P = Q := by
  classical

  let P₀ : SchemeHomOver (E.lev ≫ E.f) E.f := ⟨E.lev, rfl⟩
  have hP₀ : FactorsThrough E.lev P₀ := ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨c, hc⟩ := hlev _ P₀ hP₀

  have hc' : c ≫ E'.lev = E.lev ≫ φ := by rw [hc]; rfl

  have hφone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt φ hφ (E.L.one t) = E'.L.one t := by
    intro T t
    set x := mapPt φ hφ (E.L.one t) with hx
    have hxx : E'.L.mul t x x = x := by rw [hx, ← hφmul, E.L.one_mul]
    letI := E'.L.pointGroup t
    have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
    exact mul_left_cancel h2

  have hinj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P P' : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E.lev P' → mapPt φ hφ P = mapPt φ hφ P' → P = P' := by
    intro T t P P' hP hP' h
    letI := E.L.pointGroup t
    letI := E'.L.pointGroup t

    have hD : FactorsThrough E.lev (E.L.mul t P (E.L.inv t P')) :=
      (E.lev_sub t P (E.L.inv t P') hP (E.lev_sub t P' P' hP' hP').2).1
    have hφhom : ∀ X Y : SchemeHomOver t E.f, mapPt φ hφ (X * Y) = mapPt φ hφ X * mapPt φ hφ Y := fun X Y => hφmul t X Y
    let Φ : SchemeHomOver t E.f →* SchemeHomOver t E'.f :=
      { toFun := mapPt φ hφ, map_one' := hφone t, map_mul' := hφhom }
    have hΦD : Φ (P * P'⁻¹) = 1 := by
      rw [map_mul, map_inv, show Φ P = Φ P' from h, mul_inv_cancel]

    have hnD : (P * P'⁻¹) ^ n = 1 := by
      rw [← nsmulPt_eq_pow, ← hψφ t]
      show mapPt ψ hψ (Φ (P * P'⁻¹)) = 1
      rw [hΦD]
      show mapPt ψ hψ (E'.L.one t) = E.L.one t
      rw [← hφone t, hψφ, nsmulPt_one']

    have hND : (P * P'⁻¹) ^ N = 1 := by
      rw [← nsmulPt_eq_pow]; exact E.lev_torsion t _ hD
    have h1 : (P * P'⁻¹) ^ Nat.gcd n N = 1 := (pow_gcd_eq_one).2 ⟨hnD, hND⟩
    rw [hn, pow_one] at h1
    exact mul_inv_eq_one.1 h1
  have hcomp' : c ≫ E'.lev ≫ E'.f = E.lev ≫ E.f := by rw [← Category.assoc, hc', Category.assoc, hφ]

  haveI : IsClosedImmersion E.lev := E.lev_closed
  haveI : IsClosedImmersion E'.lev := E'.lev_closed
  have hmono : Mono c := by
    refine ⟨fun {Z} u v huv => ?_⟩
    have hmE : Mono E.lev := ((IsClosedImmersion.iff_isFinite_and_mono E.lev).1 inferInstance).2
    rw [← cancel_mono E.lev]
    have ht : (v ≫ E.lev) ≫ E.f = (u ≫ E.lev) ≫ E.f := by
      have h1 : ∀ w : Z ⟶ E.C, (w ≫ E.lev) ≫ E.f = (w ≫ c) ≫ E'.lev ≫ E'.f := fun w => by
        simp only [Category.assoc, hcomp']
      rw [h1, h1, huv]
    have key := hinj ((u ≫ E.lev) ≫ E.f) ⟨u ≫ E.lev, rfl⟩ ⟨v ≫ E.lev, ht⟩ ⟨u, rfl⟩ ⟨v, rfl⟩
      (Subtype.ext (by
        simp only [mapPt_coe, Category.assoc]
        rw [← hc', ← Category.assoc, huv, Category.assoc]))
    exact congrArg Subtype.val key

  have hcomp : c ≫ (E'.lev ≫ E'.f) = E.lev ≫ E.f := hcomp'
  haveI : IsFinite (E'.lev ≫ E'.f) := E'.lev_finite
  haveI : IsFinite (E.lev ≫ E.f) := E.lev_finite
  haveI : IsFinite (c ≫ (E'.lev ≫ E'.f)) := by rw [hcomp]; infer_instance
  haveI : IsFinite c := IsFinite.of_comp c (E'.lev ≫ E'.f)
  haveI : IsClosedImmersion c := (IsClosedImmersion.iff_isFinite_and_mono c).2 ⟨inferInstance, hmono⟩

  haveI : Flat (E'.lev ≫ E'.f) := E'.lev_flat
  haveI : LocallyOfFinitePresentation (E'.lev ≫ E'.f) := E'.lev_finitePresentation
  haveI : Flat (E.lev ≫ E.f) := E.lev_flat
  haveI : LocallyOfFinitePresentation (E.lev ≫ E.f) := E.lev_finitePresentation
  haveI : IsIso c := AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq c (E'.lev ≫ E'.f) (E.lev ≫ E.f) hcomp
    (fun s => by rw [E.lev_rank s, E'.lev_rank s])

  intro T t Q
  constructor
  · rintro ⟨Q₀, hQ₀⟩
    refine ⟨⟨Q₀ ≫ inv c ≫ E.lev, ?_⟩, ⟨Q₀ ≫ inv c, by simp only [Category.assoc]⟩, ?_⟩
    · simp only [Category.assoc]
      rw [← hcomp', IsIso.inv_hom_id_assoc, ← Category.assoc, hQ₀]
      exact Q.2
    · apply Subtype.ext
      simp only [mapPt_coe, Category.assoc]
      rw [← hc', IsIso.inv_hom_id_assoc, hQ₀]
  · rintro ⟨P, hP, rfl⟩
    exact hlev t P hP

end S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime (solution)
