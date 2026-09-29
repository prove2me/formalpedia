-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isPullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/bf628348-c84a-556b-9e8a-5cd7c1a9eb2e

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isPullback_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace ALBaseChange

variable {S S' : Type u} [CommRing S] [CommRing S'] {φ : S →+* S'}

section Square

variable {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}

def img (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{u}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem img_coe (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{u}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') : (img hg P).1 = P.1 ≫ g := rfl

theorem img_injective (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{u}}
    {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' f'} (h : img hg P = img hg Q) : P = Q := by
  apply Subtype.ext
  apply hg.hom_ext
  · exact congrArg Subtype.val h
  · rw [P.2, Q.2]

theorem img_one (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    img hg (L'.one t') = L.one (t' ≫ Spec.map (CommRingCat.ofHom φ)) := by
  set x := img hg (L'.one t') with hx
  have hxx : L.mul _ x x = x := by
    apply Subtype.ext
    rw [hx, ← hg_mul, L'.one_mul]
    rfl
  letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem eq_one_iff (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    P = L'.one t' ↔ img hg P = L.one (t' ≫ Spec.map (CommRingCat.ofHom φ)) := by
  constructor
  · rintro rfl; exact img_one hg L L' hg_mul t'
  · intro h; exact img_injective hg (h.trans (img_one hg L L' hg_mul t').symm)

theorem img_mul (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    img hg (L'.mul t' P Q) = L.mul _ (img hg P) (img hg Q) :=
  Subtype.ext (hg_mul t' P Q)

theorem img_pushPt (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (a : A ⟶ A) (ha : a ≫ f = f) (a' : A' ⟶ A') (ha' : a' ≫ f' = f') (hcomm : a' ≫ g = g ≫ a)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    img hg (pushPt a' ha' P) = pushPt a ha (img hg P) := by
  apply Subtype.ext
  simp only [img_coe, pushPt, mapPt_coe, Category.assoc, hcomm]

end Square

section TwoSquares

variable {A A' B B' : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of S)} {fA' : A' ⟶ Spec (CommRingCat.of S')}
  {fB : B ⟶ Spec (CommRingCat.of S)} {fB' : B' ⟶ Spec (CommRingCat.of S')} {gA : A' ⟶ A} {gB : B' ⟶ B}

theorem img_mapPt (hgA : IsPullback gA fA' fA (Spec.map (CommRingCat.ofHom φ)))
    (hgB : IsPullback gB fB' fB (Spec.map (CommRingCat.ofHom φ)))
    (θ : A ⟶ B) (hθ : θ ≫ fB = fA) (θ' : A' ⟶ B') (hθ' : θ' ≫ fB' = fA') (hcomm : θ' ≫ gB = gA ≫ θ)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' fA') :
    img hgB (mapPt θ' hθ' P) = mapPt θ hθ (img hgA P) := by
  apply Subtype.ext
  simp only [img_coe, mapPt_coe, Category.assoc, hcomm]

end TwoSquares

end ALBaseChange
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isPullback_of_isPullback.ALBaseChange"

open ALBaseChange CerednikDrinfeld QuaternionAlgebra in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : QM.FakeEllipticCurve Λ N S) (E' E'' : QM.FakeEllipticCurve Λ N S')
    (h' : QM.FakeEllipticCurve.IsPullback φ E E') (h'' : QM.FakeEllipticCurve.IsPullback φ E E'') :
    QM.FakeEllipticCurve.Iso E' E'' := by
  obtain ⟨g', hg', m', a', l'⟩ := h'
  obtain ⟨g'', hg'', m'', a'', l''⟩ := h''
  let eh : E'.A ⟶ E''.A := hg''.lift g' E'.f hg'.w
  have eh_fst : eh ≫ g'' = g' := hg''.lift_fst _ _ _
  have eh_snd : eh ≫ E''.f = E'.f := hg''.lift_snd _ _ _
  let ei : E''.A ⟶ E'.A := hg'.lift g'' E''.f hg''.w
  have ei_fst : ei ≫ g' = g'' := hg'.lift_fst _ _ _
  have ei_snd : ei ≫ E'.f = E''.f := hg'.lift_snd _ _ _
  let e : E'.A ≅ E''.A :=
    { hom := eh, inv := ei,
      hom_inv_id := by
        apply hg'.hom_ext
        · rw [Category.assoc, ei_fst, eh_fst, Category.id_comp]
        · rw [Category.assoc, ei_snd, eh_snd, Category.id_comp]
      inv_hom_id := by
        apply hg''.hom_ext
        · rw [Category.assoc, eh_fst, ei_fst, Category.id_comp]
        · rw [Category.assoc, eh_snd, ei_snd, Category.id_comp] }
  have he : e.hom ≫ E''.f = E'.f := eh_snd

  have timg : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t E'.f),
      img hg'' (mapPt e.hom he P) = img hg' P := by
    intro T t P
    apply Subtype.ext
    simp only [img_coe, mapPt_coe, Category.assoc]
    rw [eh_fst]
  refine ⟨e, he, ?_, ?_, ?_⟩
  · intro T t P Q
    apply img_injective hg''
    rw [timg, img_mul hg' E.L E'.L m', img_mul hg'' E.L E''.L m'', timg, timg]
  · intro x
    apply hg''.hom_ext
    · rw [Category.assoc, eh_fst, a', Category.assoc, a'', ← Category.assoc, eh_fst]
    · rw [Category.assoc, he, E'.act_over, Category.assoc, E''.act_over, he]
  · intro T t P
    constructor
    · intro hP
      obtain ⟨P₀, hP₀⟩ := l' t P hP
      apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
        φ E E'' g'' hg'' m'' l'' t (mapPt e.hom he P)
      exact ⟨P₀, by rw [hP₀]; exact (congrArg Subtype.val (timg P)).symm⟩
    · intro hP
      obtain ⟨P₀, hP₀⟩ := l'' t (mapPt e.hom he P) hP
      apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
        φ E E' g' hg' m' l' t P
      exact ⟨P₀, by rw [hP₀]; exact congrArg Subtype.val (timg P)⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isPullback_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isPullback_of_isPullback (solution)
