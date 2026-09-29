-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isAtkinLehnerQuotient_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/185daa55-6909-5f7c-b5a0-cfbbdcf8d5e2

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_isPullback

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_isPullback.ALBaseChange"

namespace ALTBaseChange

open CerednikDrinfeld.QM.FakeEllipticCurve

theorem factorsThrough_levK_of_exists_comp_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : WithExtraLevel Λ N ℓ S) (u' : WithExtraLevel Λ N ℓ S')
    (g : u'.1.A ⟶ u.1.A) (hg : CategoryTheory.IsPullback g u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ)))
    (hg_levK : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough u'.2.levK P → ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f)
    (hP : ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g) : FactorsThrough u'.2.levK P := by
  classical
  haveI := u.2.levK_closed
  haveI := u'.2.levK_closed
  haveI := u.2.levK_finite
  haveI := u.2.levK_flat
  haveI := u.2.levK_finitePresentation
  haveI := u'.2.levK_finite
  haveI := u'.2.levK_flat
  haveI := u'.2.levK_finitePresentation
  have hB : IsPullback (pullback.fst u.2.levK g) (pullback.snd u.2.levK g ≫ u'.1.f) (u.2.levK ≫ u.1.f)
      (Spec.map (CommRingCat.ofHom φ)) :=
    ((IsPullback.of_hasPullback u.2.levK g).flip.paste_horiz hg.flip).flip
  haveI hYfin : IsFinite (pullback.snd u.2.levK g ≫ u'.1.f) := MorphismProperty.of_isPullback hB u.2.levK_finite
  haveI hYfl : Flat (pullback.snd u.2.levK g ≫ u'.1.f) := MorphismProperty.of_isPullback hB u.2.levK_flat
  haveI hYfp : LocallyOfFinitePresentation (pullback.snd u.2.levK g ≫ u'.1.f) :=
    MorphismProperty.of_isPullback hB u.2.levK_finitePresentation
  obtain ⟨c₀, hc₀⟩ := hg_levK (u'.2.levK ≫ u'.1.f) ⟨u'.2.levK, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩
  let i : u'.2.K ⟶ pullback u.2.levK g := pullback.lift c₀ u'.2.levK hc₀
  have hi : i ≫ pullback.snd u.2.levK g = u'.2.levK := pullback.lift_snd _ _ _
  haveI : IsClosedImmersion (i ≫ pullback.snd u.2.levK g) := by rw [hi]; exact u'.2.levK_closed
  haveI : IsClosedImmersion i := IsClosedImmersion.of_comp_isClosedImmersion i (pullback.snd u.2.levK g)
  have hw : i ≫ (pullback.snd u.2.levK g ≫ u'.1.f) = u'.2.levK ≫ u'.1.f := by rw [← Category.assoc, hi]
  have hrk : ∀ s : ↥(Spec (CommRingCat.of S')),
      (u'.2.levK ≫ u'.1.f).finrank s = (pullback.snd u.2.levK g ≫ u'.1.f).finrank s := by
    intro s
    rw [u'.2.levK_rank s, Scheme.Hom.finrank_of_isPullback _ _ _ _ hB s, u.2.levK_rank]
  haveI hiso : IsIso i :=
    AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq i (pullback.snd u.2.levK g ≫ u'.1.f) (u'.2.levK ≫ u'.1.f)
      hw hrk
  obtain ⟨P₀, hP₀⟩ := hP
  refine ⟨pullback.lift P₀ P.1 hP₀ ≫ inv i, ?_⟩
  rw [Category.assoc, ← hi, IsIso.inv_hom_id_assoc, pullback.lift_snd]

end ALTBaseChange
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_isPullback.ALBaseChange"

open ALBaseChange CerednikDrinfeld QuaternionAlgebra in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (r : ℕ)
    (v v₁ : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (v' v₁' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (hv : (∃ (g : v'.1.A ⟶ v.1.A)
        (hg : CategoryTheory.IsPullback g v'.1.f v.1.f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q Q' : SchemeHomOver t' v'.1.f),
        (v'.1.L.mul t' Q Q').1 ≫ g =
          (v.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩
            ⟨Q'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q'.2]⟩).1) ∧
      (∀ x : ↥Λ, v'.1.act x ≫ g = g ≫ v.1.act x) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q : SchemeHomOver t' v'.1.f),
        (QM.FactorsThrough v'.1.lev Q → ∃ Q₀ : T ⟶ v.1.C, Q₀ ≫ v.1.lev = Q.1 ≫ g) ∧
        (QM.FactorsThrough v'.2.levK Q → ∃ Q₀ : T ⟶ v.2.K, Q₀ ≫ v.2.levK = Q.1 ≫ g))))
    (hv₁ : (∃ (g : v₁'.1.A ⟶ v₁.1.A)
        (hg : CategoryTheory.IsPullback g v₁'.1.f v₁.1.f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q Q' : SchemeHomOver t' v₁'.1.f),
        (v₁'.1.L.mul t' Q Q').1 ≫ g =
          (v₁.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩
            ⟨Q'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q'.2]⟩).1) ∧
      (∀ x : ↥Λ, v₁'.1.act x ≫ g = g ≫ v₁.1.act x) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q : SchemeHomOver t' v₁'.1.f),
        (QM.FactorsThrough v₁'.1.lev Q → ∃ Q₀ : T ⟶ v₁.1.C, Q₀ ≫ v₁.1.lev = Q.1 ≫ g) ∧
        (QM.FactorsThrough v₁'.2.levK Q → ∃ Q₀ : T ⟶ v₁.2.K, Q₀ ≫ v₁.2.levK = Q.1 ≫ g))))
    (h : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r v v₁) :
    QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r v' v₁' := by
  obtain ⟨g, hg, hg_mul, hg_act, hg_lv⟩ := hv
  obtain ⟨g₁, hg₁, hg₁_mul, hg₁_act, hg₁_lv⟩ := hv₁
  have hg_lev := fun {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' v'.1.f) => (hg_lv t' P).1
  have hg_levK := fun {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' v'.1.f) => (hg_lv t' P).2
  have hg₁_lev := fun {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' v₁'.1.f) => (hg₁_lv t' P).1
  have hg₁_levK := fun {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' v₁'.1.f) => (hg₁_lv t' P).2
  obtain ⟨φr, hφr, ψr, hψr, hφhom, hψhom, hφlin, hψlin, hcomp, hker, hlev, hlevK⟩ := h
  let φ' : v'.1.A ⟶ v₁'.1.A := hg₁.lift (g ≫ φr) v'.1.f (by rw [Category.assoc, hφr]; exact hg.w)
  have hφ' : φ' ≫ v₁'.1.f = v'.1.f := hg₁.lift_snd _ _ _
  have hφ'g : φ' ≫ g₁ = g ≫ φr := hg₁.lift_fst _ _ _
  let ψ' : v₁'.1.A ⟶ v'.1.A := hg.lift (g₁ ≫ ψr) v₁'.1.f (by rw [Category.assoc, hψr]; exact hg₁.w)
  have hψ' : ψ' ≫ v'.1.f = v₁'.1.f := hg.lift_snd _ _ _
  have hψ'g : ψ' ≫ g = g₁ ≫ ψr := hg.lift_fst _ _ _
  have tφ : ∀ {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' v'.1.f),
      img hg₁ (mapPt φ' hφ' P) = mapPt φr hφr (img hg P) :=
    fun P => img_mapPt hg hg₁ φr hφr φ' hφ' hφ'g P
  have tψ : ∀ {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' v₁'.1.f),
      img hg (mapPt ψ' hψ' P) = mapPt ψr hψr (img hg₁ P) :=
    fun P => img_mapPt hg₁ hg ψr hψr ψ' hψ' hψ'g P
  refine ⟨φ', hφ', ψ', hψ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t' P Q
    apply img_injective hg₁
    rw [tφ, img_mul hg v.1.L v'.1.L hg_mul, img_mul hg₁ v₁.1.L v₁'.1.L hg₁_mul, tφ, tφ]
    exact hφhom _ _ _
  · intro T t' P Q
    apply img_injective hg
    rw [tψ, img_mul hg₁ v₁.1.L v₁'.1.L hg₁_mul, img_mul hg v.1.L v'.1.L hg_mul, tψ, tψ]
    exact hψhom _ _ _
  · intro x
    apply hg₁.hom_ext
    · rw [Category.assoc, hφ'g, ← Category.assoc, hg_act, Category.assoc, hφlin x, Category.assoc, hg₁_act,
        ← Category.assoc φ' g₁ (v₁.1.act x), hφ'g, Category.assoc]
    · rw [Category.assoc, hφ', v'.1.act_over, Category.assoc, v₁'.1.act_over, hφ']
  · intro x
    apply hg.hom_ext
    · rw [Category.assoc, hψ'g, ← Category.assoc, hg₁_act, Category.assoc, hψlin x, Category.assoc, hg_act,
        ← Category.assoc ψ' g (v.1.act x), hψ'g, Category.assoc]
    · rw [Category.assoc, hψ', v₁'.1.act_over, Category.assoc, v'.1.act_over, hψ']
  · intro hr
    obtain ⟨h1, h2⟩ := hcomp hr
    constructor
    · apply hg.hom_ext
      · rw [Category.assoc, hψ'g, ← Category.assoc, hφ'g, Category.assoc, h1, hg_act]
      · rw [Category.assoc, hψ', hφ', v'.1.act_over]
    · apply hg₁.hom_ext
      · rw [Category.assoc, hφ'g, ← Category.assoc, hψ'g, Category.assoc, h2, hg₁_act]
      · rw [Category.assoc, hφ', hψ', v₁'.1.act_over]
  · intro T t' P
    rw [eq_one_iff hg₁ v₁.1.L v₁'.1.L hg₁_mul, tφ, hker]
    refine forall_congr' fun m => forall_congr' fun n => forall_congr' fun _ => ?_
    rw [eq_one_iff hg v.1.L v'.1.L hg_mul, img_pushPt hg (v.1.act m) (v.1.act_over m) (v'.1.act m) (v'.1.act_over m) (hg_act m)]
  · intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := hg_lev t' P hP
    obtain ⟨P₁, hP₁⟩ := hlev _ (img hg P) ⟨P₀, hP₀⟩
    apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
      φ v₁.1 v₁'.1 g₁ hg₁ hg₁_mul hg₁_lev t' (mapPt φ' hφ' P)
    exact ⟨P₁, by rw [hP₁]; exact congrArg Subtype.val (tφ P).symm⟩
  · intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := hg_levK t' P hP
    obtain ⟨P₁, hP₁⟩ := hlevK _ (img hg P) ⟨P₀, hP₀⟩
    apply ALTBaseChange.factorsThrough_levK_of_exists_comp_eq φ v₁ v₁' g₁ hg₁ hg₁_levK t' (mapPt φ' hφ' P)
    exact ⟨P₁, by rw [hP₁]; exact congrArg Subtype.val (tφ P).symm⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_isPullback (solution)
