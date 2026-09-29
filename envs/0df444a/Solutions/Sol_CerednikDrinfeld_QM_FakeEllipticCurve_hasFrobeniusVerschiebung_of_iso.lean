-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1892aeb9-f888-5ff2-ae19-07c17280b604

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_iso

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace HeckeTFV

variable {R : Type u} [CommRing R]

theorem mapPt_comp {A A' A'' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (χ : A' ⟶ A'') (hφ : φ ≫ f' = f) (hχ : χ ≫ f'' = f')
    (h : (φ ≫ χ) ≫ f'' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ χ) h P = mapPt χ hχ (mapPt φ hφ P) :=
  Subtype.ext (by simp [mapPt_coe, Category.assoc])

theorem mapPt_congr {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {φ φ' : A ⟶ A'} (hφ : φ ≫ f' = f) (hφ' : φ' ≫ f' = f) (h : φ = φ')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt φ' hφ' P := by subst h; rfl

theorem mapPt_id {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (h : 𝟙 A ≫ f = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (𝟙 A) h P = P := Subtype.ext (by simp [mapPt_coe])

theorem mul_val_congr {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {X X' Y Y' : SchemeHomOver t f}
    (hX : X.1 = X'.1) (hY : Y.1 = Y'.1) : (L.mul t X Y).1 = (L.mul t X' Y').1 := by
  rw [Subtype.ext hX, Subtype.ext hY]

theorem mapPt_one {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  letI := L'.pointGroup t
  have h := hmul t (L.one t) (L.one t)
  rw [L.one_mul] at h
  have h' : mapPt φ hφ (L.one t) = mapPt φ hφ (L.one t) * mapPt φ hφ (L.one t) := h
  exact (mul_eq_left.mp h'.symm)

theorem mapPt_nsmulPt {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one L L' φ hφ hmul t
  | succ n ih =>
    show mapPt φ hφ (L.mul t (nsmulPt L t n P) P) = L'.mul t (nsmulPt L' t n (mapPt φ hφ P)) (mapPt φ hφ P)
    rw [hmul, ih]

end HeckeTFV

open HeckeTFV in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S] (ℓ : ℕ) [Fact ℓ.Prime] [CharP S ℓ]
    (d d' E : FakeEllipticCurve Λ N S)
    (hD : HasFrobeniusVerschiebung ℓ d d') (he : FakeEllipticCurve.Iso d' E) :
    HasFrobeniusVerschiebung ℓ d E := by
  classical
  obtain ⟨D⟩ := hD
  obtain ⟨e, he, hemul, heact, helev⟩ := he
  have hei : e.inv ≫ d'.f = E.f := by rw [← he, e.inv_hom_id_assoc]
  have hid' : 𝟙 d'.A ≫ d'.f = d'.f := Category.id_comp _
  have hidE : 𝟙 E.A ≫ E.f = E.f := Category.id_comp _

  have hrt1 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f),
      mapPt e.hom he (mapPt e.inv hei P) = P := by
    intro T t P
    rw [← mapPt_comp e.inv e.hom hei he (by rw [e.inv_hom_id]; exact hidE), mapPt_congr _ hidE e.inv_hom_id, mapPt_id]
  have hrt2 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t d'.f),
      mapPt e.inv hei (mapPt e.hom he P) = P := by
    intro T t P
    rw [← mapPt_comp e.hom e.inv he hei (by rw [e.hom_inv_id]; exact hid'), mapPt_congr _ hid' e.hom_inv_id, mapPt_id]

  have heimul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.inv hei (E.L.mul t P Q) = d'.L.mul t (mapPt e.inv hei P) (mapPt e.inv hei Q) := by
    intro T t P Q
    have h := hemul t (mapPt e.inv hei P) (mapPt e.inv hei Q)
    rw [hrt1, hrt1] at h
    rw [← h, hrt2]
  have heinv_act : ∀ x : ↥Λ, E.act x ≫ e.inv = e.inv ≫ d'.act x := by
    intro x
    rw [← cancel_epi e.hom, ← Category.assoc, ← heact, Category.assoc, e.hom_inv_id, Category.comp_id, e.hom_inv_id_assoc]
  have heilev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P ↔ FactorsThrough d'.lev (mapPt e.inv hei P) := by
    intro T t P
    rw [helev t (mapPt e.inv hei P), hrt1]

  have hsq : IsPullback (e.inv ≫ D.pr) E.f d.f (Spec.map (CommRingCat.ofHom (frobenius S ℓ))) := by
    have h1 : IsPullback e.inv E.f d'.f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [hei, Category.comp_id]⟩
    have := h1.paste_horiz D.pr_isPullback
    rwa [Category.id_comp] at this
  have hFo : (D.F ≫ e.hom) ≫ E.f = d.f := by rw [Category.assoc, he, D.F_over]
  have hVo : (e.inv ≫ D.V) ≫ d.f = E.f := by rw [Category.assoc, D.V_over, hei]
  refine ⟨{
    pr := e.inv ≫ D.pr
    pr_isPullback := hsq
    pr_mul := ?_
    pr_act := ?_
    pr_lev := ?_
    F := D.F ≫ e.hom
    F_over := hFo
    V := e.inv ≫ D.V
    V_over := hVo
    F_hom := ?_
    V_hom := ?_
    F_act := fun x => by rw [← Category.assoc, D.F_act, Category.assoc, heact, Category.assoc]
    V_act := fun x => by rw [← Category.assoc, heinv_act, Category.assoc, D.V_act, Category.assoc]
    F_lev := ?_
    V_lev := ?_
    V_F := ?_
    F_V := ?_
    F_frobenius := ?_ }⟩
  ·
    intro T t' P Q
    have h := D.pr_mul t' (mapPt e.inv hei P) (mapPt e.inv hei Q)
    rw [← heimul, mapPt_coe, Category.assoc] at h
    rw [h]
    exact mul_val_congr d.L _ (by simp [mapPt_coe, Category.assoc]) (by simp [mapPt_coe, Category.assoc])
  ·
    intro x
    rw [← Category.assoc, heinv_act, Category.assoc, D.pr_act, Category.assoc]
  ·
    intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := D.pr_lev t' (mapPt e.inv hei P) ((heilev t' P).mp hP)
    exact ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc]⟩
  ·
    intro T t P Q
    rw [mapPt_comp D.F e.hom D.F_over he, mapPt_comp D.F e.hom D.F_over he, mapPt_comp D.F e.hom D.F_over he, D.F_hom, hemul]
  ·
    intro T t P Q
    rw [mapPt_comp e.inv D.V hei D.V_over, mapPt_comp e.inv D.V hei D.V_over, mapPt_comp e.inv D.V hei D.V_over, heimul, D.V_hom]
  ·
    intro T t P hP
    rw [mapPt_comp D.F e.hom D.F_over he]
    exact (helev t _).mp (D.F_lev t P hP)
  ·
    intro T t P hP
    rw [mapPt_comp e.inv D.V hei D.V_over]
    exact D.V_lev t _ ((heilev t P).mp hP)
  ·
    intro T t P
    rw [mapPt_comp D.F e.hom D.F_over he, mapPt_comp e.inv D.V hei D.V_over, hrt2]
    exact D.V_F t P
  ·
    intro T t Q
    rw [mapPt_comp e.inv D.V hei D.V_over, mapPt_comp D.F e.hom D.F_over he, D.F_V,
      mapPt_nsmulPt d'.L E.L e.hom he hemul, hrt1]
  ·
    intro B _ _ x
    rw [Category.assoc, e.hom_inv_id_assoc, ← Category.assoc]
    have := D.F_frobenius B x
    rw [← Category.assoc] at this
    exact this

end S_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_iso
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_iso (solution)
