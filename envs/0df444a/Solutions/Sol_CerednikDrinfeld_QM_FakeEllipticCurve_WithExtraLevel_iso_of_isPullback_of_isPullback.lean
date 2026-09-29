-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isPullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7bb0c7d4-28d2-55f9-8a5c-b8004401244a

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_levK_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace ALBaseChange

variable {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}

section Square

variable {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}

def img (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem img_coe (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') : (img hg P).1 = P.1 ≫ g := rfl

theorem img_injective (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' f'} (h : img hg P = img hg Q) : P = Q := by
  apply Subtype.ext
  apply hg.hom_ext
  · exact congrArg Subtype.val h
  · rw [P.2, Q.2]

theorem img_one (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) :
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
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    P = L'.one t' ↔ img hg P = L.one (t' ≫ Spec.map (CommRingCat.ofHom φ)) := by
  constructor
  · rintro rfl; exact img_one hg L L' hg_mul t'
  · intro h; exact img_injective hg (h.trans (img_one hg L L' hg_mul t').symm)

theorem img_mul (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    img hg (L'.mul t' P Q) = L.mul _ (img hg P) (img hg Q) :=
  Subtype.ext (hg_mul t' P Q)

theorem img_pushPt (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (a : A ⟶ A) (ha : a ≫ f = f) (a' : A' ⟶ A') (ha' : a' ≫ f' = f') (hcomm : a' ≫ g = g ≫ a)
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    img hg (pushPt a' ha' P) = pushPt a ha (img hg P) := by
  apply Subtype.ext
  simp only [img_coe, pushPt, mapPt_coe, Category.assoc, hcomm]

end Square

section TwoSquares

variable {A A' B B' : Scheme.{0}} {fA : A ⟶ Spec (CommRingCat.of S)} {fA' : A' ⟶ Spec (CommRingCat.of S')}
  {fB : B ⟶ Spec (CommRingCat.of S)} {fB' : B' ⟶ Spec (CommRingCat.of S')} {gA : A' ⟶ A} {gB : B' ⟶ B}

theorem img_mapPt (hgA : IsPullback gA fA' fA (Spec.map (CommRingCat.ofHom φ)))
    (hgB : IsPullback gB fB' fB (Spec.map (CommRingCat.ofHom φ)))
    (θ : A ⟶ B) (hθ : θ ≫ fB = fA) (θ' : A' ⟶ B') (hθ' : θ' ≫ fB' = fA') (hcomm : θ' ≫ gB = gA ≫ θ)
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' fA') :
    img hgB (mapPt θ' hθ' P) = mapPt θ hθ (img hgA P) := by
  apply Subtype.ext
  simp only [img_coe, mapPt_coe, Category.assoc, hcomm]

end TwoSquares

end ALBaseChange
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback.ALBaseChange"

open ALBaseChange CerednikDrinfeld QuaternionAlgebra in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' u'' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (h' : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u') (h'' : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u'') :
    FakeEllipticCurve.WithExtraLevel.Iso u' u'' := by
  obtain ⟨g', hg', m', a', l'⟩ := h'
  obtain ⟨g'', hg'', m'', a'', l''⟩ := h''
  let eh : u'.1.A ⟶ u''.1.A := hg''.lift g' u'.1.f hg'.w
  have eh_fst : eh ≫ g'' = g' := hg''.lift_fst _ _ _
  have eh_snd : eh ≫ u''.1.f = u'.1.f := hg''.lift_snd _ _ _
  let ei : u''.1.A ⟶ u'.1.A := hg'.lift g'' u''.1.f hg''.w
  have ei_fst : ei ≫ g' = g'' := hg'.lift_fst _ _ _
  have ei_snd : ei ≫ u'.1.f = u''.1.f := hg'.lift_snd _ _ _
  let e : u'.1.A ≅ u''.1.A :=
    { hom := eh, inv := ei,
      hom_inv_id := by
        apply hg'.hom_ext
        · rw [Category.assoc, ei_fst, eh_fst, Category.id_comp]
        · rw [Category.assoc, ei_snd, eh_snd, Category.id_comp]
      inv_hom_id := by
        apply hg''.hom_ext
        · rw [Category.assoc, eh_fst, ei_fst, Category.id_comp]
        · rw [Category.assoc, eh_snd, ei_snd, Category.id_comp] }
  have he : e.hom ≫ u''.1.f = u'.1.f := eh_snd
  have timg : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t u'.1.f),
      img hg'' (mapPt e.hom he P) = img hg' P := by
    intro T t P
    apply Subtype.ext
    simp only [img_coe, mapPt_coe, Category.assoc]
    rw [eh_fst]
  have l'1 : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough u'.1.lev P → ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g' := fun t' P => (l' t' P).1
  have l''1 : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u''.1.f),
      FactorsThrough u''.1.lev P → ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g'' := fun t' P => (l'' t' P).1
  have l'2 : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough u'.2.levK P → ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g' := fun t' P => (l' t' P).2
  have l''2 : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u''.1.f),
      FactorsThrough u''.2.levK P → ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g'' := fun t' P => (l'' t' P).2
  refine ⟨e, he, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    apply img_injective hg''
    rw [timg, img_mul hg' u.1.L u'.1.L m', img_mul hg'' u.1.L u''.1.L m'', timg, timg]
  · intro x
    apply hg''.hom_ext
    · rw [Category.assoc, eh_fst, a', Category.assoc, a'', ← Category.assoc, eh_fst]
    · rw [Category.assoc, he, u'.1.act_over, Category.assoc, u''.1.act_over, he]
  · intro T t P
    constructor
    · intro hP
      obtain ⟨P₀, hP₀⟩ := l'1 t P hP
      apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
        φ u.1 u''.1 g'' hg'' m'' l''1 t (mapPt e.hom he P)
      exact ⟨P₀, by rw [hP₀]; exact (congrArg Subtype.val (timg P)).symm⟩
    · intro hP
      obtain ⟨P₀, hP₀⟩ := l''1 t (mapPt e.hom he P) hP
      apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
        φ u.1 u'.1 g' hg' m' l'1 t P
      exact ⟨P₀, by rw [hP₀]; exact congrArg Subtype.val (timg P)⟩
  · intro T t P
    constructor
    · intro hP
      obtain ⟨P₀, hP₀⟩ := l'2 t P hP
      apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_levK_of_exists_comp_eq_of_isPullback
        φ u u'' g'' hg'' l''2 t (mapPt e.hom he P)
      exact ⟨P₀, by rw [hP₀]; exact (congrArg Subtype.val (timg P)).symm⟩
    · intro hP
      obtain ⟨P₀, hP₀⟩ := l''2 t (mapPt e.hom he P) hP
      apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_levK_of_exists_comp_eq_of_isPullback
        φ u u' g' hg' l'2 t P
      exact ⟨P₀, by rw [hP₀]; exact congrArg Subtype.val (timg P)⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback (solution)
