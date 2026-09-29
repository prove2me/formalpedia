-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_factorsThrough_lev_mapPt_eq_of_forall_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/833e0a78-c928-54e6-b527-a97f75918a99

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_factorsThrough_lev_mapPt_eq_of_forall_eq_one

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open CategoryTheory.Limits GoodReductionJacobian CerednikDrinfeld.QM.FakeEllipticCurve

universe u

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
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (k : Type) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0)
    (E E' : FakeEllipticCurve Λ N k) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hinj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E'.L.one t → FactorsThrough E.lev P → P = E.L.one t)
    (hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P)) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      FactorsThrough E'.lev Q → ∃ P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt φ hφ P = Q := by
  classical

  let P₀ : SchemeHomOver (E.lev ≫ E.f) E.f := ⟨E.lev, rfl⟩
  have hP₀ : FactorsThrough E.lev P₀ := ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨c, hc⟩ := hlev _ P₀ hP₀
  have hc' : c ≫ E'.lev = E.lev ≫ φ := by rw [hc]; rfl
  have hφone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), mapPt φ hφ (E.L.one t) = E'.L.one t := by
    intro T t
    set x := mapPt φ hφ (E.L.one t) with hx
    have hxx : E'.L.mul t x x = x := by rw [hx, ← hmul, E.L.one_mul]
    letI := E'.L.pointGroup t
    have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
    exact mul_left_cancel h2

  have hinj2 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P P' : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E.lev P' → mapPt φ hφ P = mapPt φ hφ P' → P = P' := by
    intro T t P P' hP hP' h
    letI := E.L.pointGroup t
    letI := E'.L.pointGroup t
    have hD : FactorsThrough E.lev (E.L.mul t P (E.L.inv t P')) :=
      (E.lev_sub t P (E.L.inv t P') hP (E.lev_sub t P' P' hP' hP').2).1
    have hφhom : ∀ X Y : SchemeHomOver t E.f, mapPt φ hφ (X * Y) = mapPt φ hφ X * mapPt φ hφ Y := fun X Y => hmul t X Y
    let Φ : SchemeHomOver t E.f →* SchemeHomOver t E'.f :=
      { toFun := mapPt φ hφ, map_one' := hφone t, map_mul' := hφhom }
    have hΦD : Φ (P * P'⁻¹) = 1 := by
      rw [map_mul, map_inv, show Φ P = Φ P' from h, mul_inv_cancel]
    have h1 : P * P'⁻¹ = 1 := hinj t (E.L.mul t P (E.L.inv t P')) hΦD hD
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
    have key := hinj2 ((u ≫ E.lev) ≫ E.f) ⟨u ≫ E.lev, rfl⟩ ⟨v ≫ E.lev, ht⟩ ⟨u, rfl⟩ ⟨v, rfl⟩
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

  intro T t Q hQ
  obtain ⟨Q₀, hQ₀⟩ := hQ
  refine ⟨⟨Q₀ ≫ inv c ≫ E.lev, ?_⟩, ⟨Q₀ ≫ inv c, by simp only [Category.assoc]⟩, ?_⟩
  · simp only [Category.assoc]
    rw [← hcomp', IsIso.inv_hom_id_assoc, ← Category.assoc, hQ₀]
    exact Q.2
  · apply Subtype.ext
    simp only [mapPt_coe, Category.assoc]
    rw [← hc', IsIso.inv_hom_id_assoc, hQ₀]

#print axioms solution

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_factorsThrough_lev_mapPt_eq_of_forall_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_factorsThrough_lev_mapPt_eq_of_forall_eq_one (solution)
