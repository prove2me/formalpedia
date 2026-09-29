-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/54807e6a-5263-5326-9216-950a28ea72b8

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isPullback

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isPullback.ALBaseChange"

open ALBaseChange in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (r : ℕ)
    (E E₁ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) (E' E₁' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S')
    (hE : CerednikDrinfeld.QM.FakeEllipticCurve.IsPullback φ E E')
    (hE₁ : CerednikDrinfeld.QM.FakeEllipticCurve.IsPullback φ E₁ E₁')
    (h : CerednikDrinfeld.QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E₁) :
    CerednikDrinfeld.QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E' E₁' := by
  obtain ⟨g, hg, hg_mul, hg_act, hg_lev⟩ := hE
  obtain ⟨g₁, hg₁, hg₁_mul, hg₁_act, hg₁_lev⟩ := hE₁
  obtain ⟨φr, hφr, ψr, hψr, hφhom, hψhom, hφlin, hψlin, hcomp, hker, hlev⟩ := h

  let φ' : E'.A ⟶ E₁'.A := hg₁.lift (g ≫ φr) E'.f (by rw [Category.assoc, hφr]; exact hg.w)
  have hφ' : φ' ≫ E₁'.f = E'.f := hg₁.lift_snd _ _ _
  have hφ'g : φ' ≫ g₁ = g ≫ φr := hg₁.lift_fst _ _ _
  let ψ' : E₁'.A ⟶ E'.A := hg.lift (g₁ ≫ ψr) E₁'.f (by rw [Category.assoc, hψr]; exact hg₁.w)
  have hψ' : ψ' ≫ E'.f = E₁'.f := hg.lift_snd _ _ _
  have hψ'g : ψ' ≫ g = g₁ ≫ ψr := hg.lift_fst _ _ _

  have tφ : ∀ {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' E'.f),
      img hg₁ (mapPt φ' hφ' P) = mapPt φr hφr (img hg P) :=
    fun P => img_mapPt hg hg₁ φr hφr φ' hφ' hφ'g P
  have tψ : ∀ {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' E₁'.f),
      img hg (mapPt ψ' hψ' P) = mapPt ψr hψr (img hg₁ P) :=
    fun P => img_mapPt hg₁ hg ψr hψr ψ' hψ' hψ'g P
  refine ⟨φ', hφ', ψ', hψ', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro T t' P Q
    apply img_injective hg₁
    rw [tφ, img_mul hg E.L E'.L hg_mul, img_mul hg₁ E₁.L E₁'.L hg₁_mul, tφ, tφ]
    exact hφhom _ _ _
  ·
    intro T t' P Q
    apply img_injective hg
    rw [tψ, img_mul hg₁ E₁.L E₁'.L hg₁_mul, img_mul hg E.L E'.L hg_mul, tψ, tψ]
    exact hψhom _ _ _
  ·
    intro x
    apply hg₁.hom_ext
    · rw [Category.assoc, hφ'g, ← Category.assoc, hg_act, Category.assoc, hφlin x, Category.assoc, hg₁_act,
        ← Category.assoc φ' g₁ (E₁.act x), hφ'g, Category.assoc]
    · rw [Category.assoc, hφ', E'.act_over, Category.assoc, E₁'.act_over, hφ']
  ·
    intro x
    apply hg.hom_ext
    · rw [Category.assoc, hψ'g, ← Category.assoc, hg₁_act, Category.assoc, hψlin x, Category.assoc, hg_act,
        ← Category.assoc ψ' g (E.act x), hψ'g, Category.assoc]
    · rw [Category.assoc, hψ', E₁'.act_over, Category.assoc, E'.act_over, hψ']
  ·
    intro hr
    obtain ⟨h1, h2⟩ := hcomp hr
    constructor
    · apply hg.hom_ext
      · rw [Category.assoc, hψ'g, ← Category.assoc, hφ'g, Category.assoc, h1, hg_act]
      · rw [Category.assoc, hψ', hφ', E'.act_over]
    · apply hg₁.hom_ext
      · rw [Category.assoc, hφ'g, ← Category.assoc, hψ'g, Category.assoc, h2, hg₁_act]
      · rw [Category.assoc, hφ', hψ', E₁'.act_over]
  ·
    intro T t' P
    rw [eq_one_iff hg₁ E₁.L E₁'.L hg₁_mul, tφ, hker]
    refine forall_congr' fun m => forall_congr' fun n => forall_congr' fun _ => ?_
    rw [eq_one_iff hg E.L E'.L hg_mul, img_pushPt hg (E.act m) (E.act_over m) (E'.act m) (E'.act_over m) (hg_act m)]
  ·
    intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := hg_lev t' P hP
    obtain ⟨P₁, hP₁⟩ := hlev _ (img hg P) ⟨P₀, hP₀⟩
    apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
      φ E₁ E₁' g₁ hg₁ hg₁_mul hg₁_lev t' (mapPt φ' hφ' P)
    exact ⟨P₁, by rw [hP₁]; exact congrArg Subtype.val (tφ P).symm⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isPullback (solution)
