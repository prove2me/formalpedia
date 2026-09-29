-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.levelStructure_lev_comp_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/9de5cfa9-353f-553a-b1d6-fc0b0023475d

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_levelStructure_lev_comp_of_disjoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace LevelTransport21

variable {S : Type u} [CommRing S] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (hc' : L'.IsCommutative)
  (p : A ⟶ A') (hp : p ≫ f' = f)
  (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    mapPt p hp (L.mul t P Q) = L'.mul t (mapPt p hp P) (mapPt p hp Q))

include hhom in
theorem mapPt_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt p hp (L.one t) = L'.one t := by
  have h := hhom t (L.one t) (L.one t)
  rw [L.one_mul] at h
  have := congrArg (L'.mul t (L'.inv t (mapPt p hp (L.one t)))) h
  rw [← L'.mul_assoc, L'.inv_mul_cancel, L'.one_mul] at this
  exact this.symm

include hc' hhom in
theorem mapPt_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f) :
    mapPt p hp (L.inv t P) = L'.inv t (mapPt p hp P) := by
  have h := hhom t (L.inv t P) P
  rw [L.inv_mul_cancel, mapPt_one L L' p hp hhom] at h
  have h2 : L'.mul t (mapPt p hp (L.inv t P)) (L'.mul t (mapPt p hp P) (L'.inv t (mapPt p hp P))) =
      L'.mul t (L'.one t) (L'.inv t (mapPt p hp P)) := by
    rw [← L'.mul_assoc, ← h]
  rw [hc' t (mapPt p hp P) (L'.inv t (mapPt p hp P)), L'.inv_mul_cancel, L'.mul_one, L'.one_mul] at h2
  exact h2

include hhom in
theorem mapPt_nsmulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt p hp (nsmulPt L t n P) = nsmulPt L' t n (mapPt p hp P) := by
  induction n with
  | zero => exact mapPt_one L L' p hp hhom t
  | succ n ih =>
    show mapPt p hp (L.mul t (nsmulPt L t n P) P) = L'.mul t (nsmulPt L' t n (mapPt p hp P)) (mapPt p hp P)
    rw [hhom, ih]

end LevelTransport21

open LevelTransport21 CerednikDrinfeld.QM.FakeEllipticCurve in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S)
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f') (hc' : L'.IsCommutative)
    (act' : ↥Λ → (A' ⟶ A')) (act'_over : ∀ x : ↥Λ, act' x ≫ f' = f')
    (p : E.A ⟶ A') (hp : p ≫ f' = E.f) [IsFinite p]
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt p hp (E.L.mul t P Q) = L'.mul t (mapPt p hp P) (mapPt p hp Q))
    (hequiv : ∀ x : ↥Λ, E.act x ≫ p = p ≫ act' x)
    (hdisj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt p hp P = L'.one t → FactorsThrough E.lev P → P = E.L.one t) :
    IsClosedImmersion (E.lev ≫ p) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f'),
      FactorsThrough (E.lev ≫ p) P → FactorsThrough (E.lev ≫ p) Q →
        FactorsThrough (E.lev ≫ p) (L'.mul t P Q) ∧ FactorsThrough (E.lev ≫ p) (L'.inv t P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough (E.lev ≫ p) (L'.one t)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f'),
      FactorsThrough (E.lev ≫ p) P → nsmulPt L' t N P = L'.one t) ∧
    (∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f'),
      FactorsThrough (E.lev ≫ p) P → FactorsThrough (E.lev ≫ p) (pushPt (act' x) (act'_over x) P)) ∧
    IsFinite ((E.lev ≫ p) ≫ f') ∧ Flat ((E.lev ≫ p) ≫ f') ∧ LocallyOfFinitePresentation ((E.lev ≫ p) ≫ f') ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ((E.lev ≫ p) ≫ f').finrank s = N ^ 2) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f' // FactorsThrough (E.lev ≫ p) P},
        ∀ x y : ZMod N × ZMod N, (e (x + y) : SchemeHomOver (geomPoint k sk) f') = L'.mul (geomPoint k sk) (e x) (e y)) := by
  classical
  haveI : IsClosedImmersion E.lev := E.lev_closed

  have hFT : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f'),
      FactorsThrough (E.lev ≫ p) P ↔ ∃ Q : SchemeHomOver t E.f, FactorsThrough E.lev Q ∧ mapPt p hp Q = P := by
    intro T t P
    constructor
    · rintro ⟨P₀, hP₀⟩
      refine ⟨⟨P₀ ≫ E.lev, ?_⟩, ⟨P₀, rfl⟩, Subtype.ext ?_⟩
      · rw [← hp, ← Category.assoc, Category.assoc P₀ E.lev p, hP₀]; exact P.2
      · show (P₀ ≫ E.lev) ≫ p = P.1
        rw [Category.assoc, hP₀]
    · rintro ⟨Q, ⟨Q₀, hQ₀⟩, rfl⟩
      exact ⟨Q₀, by rw [← Category.assoc, hQ₀]; rfl⟩

  have hinj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E.lev Q → mapPt p hp P = mapPt p hp Q → P = Q := by
    intro T t P Q hP hQ h
    letI := E.L.pointGroup t; letI := L'.pointGroup t
    let F : SchemeHomOver t E.f →* SchemeHomOver t f' :=
      { toFun := mapPt p hp, map_one' := mapPt_one E.L L' p hp hhom t, map_mul' := fun X Y => hhom t X Y }
    have h1 : F (P * Q⁻¹) = 1 := by
      rw [map_mul, map_inv, show F P = F Q from h, mul_inv_cancel]
    have hC : FactorsThrough E.lev (P * Q⁻¹) :=
      (E.lev_sub t P Q⁻¹ hP (E.lev_sub t Q Q hQ hQ).2).1
    exact mul_inv_eq_one.1 (hdisj t _ h1 hC)

  haveI : IsFinite (E.lev ≫ p) := inferInstance
  haveI : Mono (E.lev ≫ p) := by
    refine ⟨fun {Z} g₁ g₂ hg => ?_⟩
    rw [← cancel_mono E.lev]
    let t : Z ⟶ Spec (CommRingCat.of S) := (g₁ ≫ E.lev) ≫ E.f
    have hg' : (g₁ ≫ E.lev) ≫ p = (g₂ ≫ E.lev) ≫ p := by simpa only [Category.assoc] using hg
    have hg₂ : (g₂ ≫ E.lev) ≫ E.f = t := by
      show (g₂ ≫ E.lev) ≫ E.f = (g₁ ≫ E.lev) ≫ E.f
      rw [← hp, ← Category.assoc, ← hg', Category.assoc]
    have := hinj t ⟨g₁ ≫ E.lev, rfl⟩ ⟨g₂ ≫ E.lev, hg₂⟩ ⟨g₁, rfl⟩ ⟨g₂, rfl⟩ (Subtype.ext hg')
    exact congrArg Subtype.val this
  have hclosed : IsClosedImmersion (E.lev ≫ p) :=
    (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨inferInstance, inferInstance⟩
  have hcomp : (E.lev ≫ p) ≫ f' = E.lev ≫ E.f := by rw [Category.assoc, hp]
  refine ⟨hclosed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro T t P Q hP hQ
    obtain ⟨P₁, hP₁, rfl⟩ := (hFT t P).1 hP
    obtain ⟨Q₁, hQ₁, rfl⟩ := (hFT t Q).1 hQ
    refine ⟨(hFT t _).2 ⟨E.L.mul t P₁ Q₁, (E.lev_sub t P₁ Q₁ hP₁ hQ₁).1, hhom t P₁ Q₁⟩,
      (hFT t _).2 ⟨E.L.inv t P₁, (E.lev_sub t P₁ P₁ hP₁ hP₁).2, mapPt_inv E.L L' hc' p hp hhom t P₁⟩⟩
  ·
    intro T t
    exact (hFT t _).2 ⟨E.L.one t, E.lev_one t, mapPt_one E.L L' p hp hhom t⟩
  ·
    intro T t P hP
    obtain ⟨P₁, hP₁, rfl⟩ := (hFT t P).1 hP
    rw [← mapPt_nsmulPt E.L L' p hp hhom, E.lev_torsion t P₁ hP₁, mapPt_one E.L L' p hp hhom]
  ·
    intro x T t P hP
    obtain ⟨P₁, hP₁, rfl⟩ := (hFT t P).1 hP
    refine (hFT t _).2 ⟨pushPt (E.act x) (E.act_over x) P₁, E.lev_stable x t P₁ hP₁, Subtype.ext ?_⟩
    show (P₁.1 ≫ E.act x) ≫ p = (P₁.1 ≫ p) ≫ act' x
    rw [Category.assoc, hequiv x, Category.assoc]
  · rw [hcomp]; exact E.lev_finite
  · rw [hcomp]; exact E.lev_flat
  · rw [hcomp]; exact E.lev_finitePresentation
  · intro s; rw [hcomp]; exact E.lev_rank s
  ·
    intro k _ _ sk hN
    obtain ⟨e, he⟩ := E.lev_fibre k sk hN
    let π : {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough E.lev P} →
        {P : SchemeHomOver (geomPoint k sk) f' // FactorsThrough (E.lev ≫ p) P} :=
      fun P => ⟨mapPt p hp P.1, (hFT _ _).2 ⟨P.1, P.2, rfl⟩⟩
    have hπ : Function.Bijective π := by
      constructor
      · intro P Q h
        apply Subtype.ext
        exact hinj _ P.1 Q.1 P.2 Q.2 (congrArg Subtype.val h)
      · intro Q
        obtain ⟨P, hP, hPQ⟩ := (hFT _ Q.1).1 Q.2
        exact ⟨⟨P, hP⟩, Subtype.ext hPQ⟩
    refine ⟨e.trans (Equiv.ofBijective π hπ), fun x y => ?_⟩
    show (mapPt p hp (e (x + y)).1) = L'.mul _ (mapPt p hp (e x).1) (mapPt p hp (e y).1)
    rw [he, hhom]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_levelStructure_lev_comp_of_disjoint
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_levelStructure_lev_comp_of_disjoint (solution)
