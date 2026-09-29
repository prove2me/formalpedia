-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/085ea3e3-28d0-55f4-9c7b-c5a4820b60c2

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {B : Type} [CommRing B] {E Ef : FakeEllipticCurve Λ N B} {d : ℕ}
    (q : E.A ⟶ Ef.A) (q' : Ef.A ⟶ E.A) (hqq' : FakeEllipticCurve.IsIsogenyPair d E Ef q q')
    {L : Type} [CommRing L] (φ : B →+* L)
    {EL EfL : FakeEllipticCurve Λ N L}
    (g : EL.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia φ E EL g)
    (gf : EfL.A ⟶ Ef.A) (hgf : FakeEllipticCurve.IsPullbackVia φ Ef EfL gf) :
    ∃ (qL : EL.A ⟶ EfL.A) (qL' : EfL.A ⟶ EL.A), qL ≫ gf = g ≫ q ∧ qL' ≫ g = gf ≫ q' ∧
      FakeEllipticCurve.IsIsogenyPair d EL EfL qL qL' := by
  classical
  obtain ⟨hq, hq', hmulq, hmulq', hactq, hactq', hcomp⟩ := hqq'
  obtain ⟨hgP, hgmul, hgact, hglev⟩ := hg
  obtain ⟨hgfP, hgfmul, hgfact, hgflev⟩ := hgf

  have mcongr : ∀ {S : Type} [CommRing S] (F : FakeEllipticCurve Λ N S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
      (P₁ P₂ Q₁ Q₂ : SchemeHomOver t F.f), P₁.1 = P₂.1 → Q₁.1 = Q₂.1 → (F.L.mul t P₁ Q₁).1 = (F.L.mul t P₂ Q₂).1 := by
    intro S _ F T t P₁ P₂ Q₁ Q₂ hP hQ
    obtain rfl : P₁ = P₂ := Subtype.ext hP
    obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
    rfl

  have wq : (g ≫ q) ≫ Ef.f = EL.f ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, hq, hgP.w]
  have wq' : (gf ≫ q') ≫ E.f = EfL.f ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, hq', hgfP.w]
  refine ⟨hgfP.lift (g ≫ q) EL.f wq, hgP.lift (gf ≫ q') EfL.f wq', hgfP.lift_fst _ _ _, hgP.lift_fst _ _ _, ?_⟩
  have hqL : hgfP.lift (g ≫ q) EL.f wq ≫ gf = g ≫ q := hgfP.lift_fst _ _ _
  have hqLf : hgfP.lift (g ≫ q) EL.f wq ≫ EfL.f = EL.f := hgfP.lift_snd _ _ _
  have hqL' : hgP.lift (gf ≫ q') EfL.f wq' ≫ g = gf ≫ q' := hgP.lift_fst _ _ _
  have hqL'f : hgP.lift (gf ≫ q') EfL.f wq' ≫ EL.f = EfL.f := hgP.lift_snd _ _ _
  set qL := hgfP.lift (g ≫ q) EL.f wq with hqLdef
  set qL' := hgP.lift (gf ≫ q') EfL.f wq' with hqL'def
  refine ⟨hqLf, hqL'f, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    apply Subtype.ext
    apply hgfP.hom_ext
    · have pP : (P.1 ≫ g) ≫ E.f = t ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, hgP.w, ← Category.assoc, P.2]
      have pQ : (Q.1 ≫ g) ≫ E.f = t ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, hgP.w, ← Category.assoc, Q.2]
      have e := congrArg Subtype.val (hmulq (t ≫ Spec.map (CommRingCat.ofHom φ)) ⟨P.1 ≫ g, pP⟩ ⟨Q.1 ≫ g, pQ⟩)
      rw [mapPt_coe] at e
      have lhs : ((EL.L.mul t P Q).1 ≫ qL) ≫ gf =
          (Ef.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ)) (mapPt q hq ⟨P.1 ≫ g, pP⟩) (mapPt q hq ⟨Q.1 ≫ g, pQ⟩)).1 := by
        rw [Category.assoc, hqL, ← Category.assoc]
        exact (congrArg (· ≫ q) (hgmul t P Q)).trans e
      rw [mapPt_coe, lhs, hgfmul t]
      exact mcongr Ef _ _ _ _ _
        (show (P.1 ≫ g) ≫ q = (P.1 ≫ qL) ≫ gf by rw [Category.assoc, Category.assoc, hqL])
        (show (Q.1 ≫ g) ≫ q = (Q.1 ≫ qL) ≫ gf by rw [Category.assoc, Category.assoc, hqL])
    · rw [mapPt_coe, Category.assoc, hqLf, (EL.L.mul t P Q).2, (EfL.L.mul t _ _).2]
  · intro T t P Q
    apply Subtype.ext
    apply hgP.hom_ext
    · have pP : (P.1 ≫ gf) ≫ Ef.f = t ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, hgfP.w, ← Category.assoc, P.2]
      have pQ : (Q.1 ≫ gf) ≫ Ef.f = t ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, hgfP.w, ← Category.assoc, Q.2]
      have e := congrArg Subtype.val (hmulq' (t ≫ Spec.map (CommRingCat.ofHom φ)) ⟨P.1 ≫ gf, pP⟩ ⟨Q.1 ≫ gf, pQ⟩)
      rw [mapPt_coe] at e
      have lhs : ((EfL.L.mul t P Q).1 ≫ qL') ≫ g =
          (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ)) (mapPt q' hq' ⟨P.1 ≫ gf, pP⟩) (mapPt q' hq' ⟨Q.1 ≫ gf, pQ⟩)).1 := by
        rw [Category.assoc, hqL', ← Category.assoc]
        exact (congrArg (· ≫ q') (hgfmul t P Q)).trans e
      rw [mapPt_coe, lhs, hgmul t]
      exact mcongr E _ _ _ _ _
        (show (P.1 ≫ gf) ≫ q' = (P.1 ≫ qL') ≫ g by rw [Category.assoc, Category.assoc, hqL'])
        (show (Q.1 ≫ gf) ≫ q' = (Q.1 ≫ qL') ≫ g by rw [Category.assoc, Category.assoc, hqL'])
    · rw [mapPt_coe, Category.assoc, hqL'f, (EfL.L.mul t P Q).2, (EL.L.mul t _ _).2]
  ·
    intro x
    apply hgfP.hom_ext
    · rw [Category.assoc, Category.assoc, hqL, hgfact x, reassoc_of% hqL, reassoc_of% (hgact x), hactq x]
    · rw [Category.assoc, Category.assoc, hqLf, EL.act_over, EfL.act_over, hqLf]
  · intro x
    apply hgP.hom_ext
    · rw [Category.assoc, Category.assoc, hqL', hgact x, reassoc_of% hqL', reassoc_of% (hgfact x), hactq' x]
    · rw [Category.assoc, Category.assoc, hqL'f, EfL.act_over, EL.act_over, hqL'f]
  ·
    intro hd
    obtain ⟨h₁, h₂⟩ := hcomp hd
    constructor
    · apply hgP.hom_ext
      · rw [Category.assoc, hqL', reassoc_of% hqL, h₁, hgact]
      · rw [Category.assoc, hqL'f, hqLf, EL.act_over]
    · apply hgfP.hom_ext
      · rw [Category.assoc, hqL, reassoc_of% hqL', h₂, hgfact]
      · rw [Category.assoc, hqLf, hqL'f, EfL.act_over]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia (solution)
