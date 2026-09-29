-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_mapPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a0cbe51a-8fc4-5ca2-836e-6953a8448909

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace L2cBody

open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

variable {S : Type u} [CommRing S] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}

theorem mapPt_injective (e : A ≅ A') (he : e.hom ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    {P Q : SchemeHomOver t f} (h : mapPt e.hom he P = mapPt e.hom he Q) : P = Q := by
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [mapPt_coe] at this
  exact (cancel_mono e.hom).mp this

theorem mapPt_mapPt_inv (e : A ≅ A') (he : e.hom ≫ f' = f) (he' : e.inv ≫ f = f') {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t f') : mapPt e.hom he (mapPt e.inv he' Q) = Q := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem mapPt_sectionAt (e : A ≅ A') (he : e.hom ≫ f' = f)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) (k : Type u) [Field k] (sk : S →+* k) :
    mapPt e.hom he (sectionAt P k sk) = sectionAt (mapPt e.hom he P) k sk := by
  apply Subtype.ext
  simp only [mapPt_coe, sectionAt, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]

theorem mapPt_pushPt (e : A ≅ A') (he : e.hom ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (φ : A ⟶ A) (hφ : φ ≫ f = f) (φ' : A' ⟶ A') (hφ' : φ' ≫ f' = f') (hcomm : φ ≫ e.hom = e.hom ≫ φ')
    (Q : SchemeHomOver t f) :
    mapPt e.hom he (pushPt φ hφ Q) = pushPt φ' hφ' (mapPt e.hom he Q) := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc, hcomm]

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N N' : ℕ}

theorem mapPt_one (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N' S)
    (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    mapPt e.hom he (E.L.one t) = E'.L.one t := by
  have h := hmul t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  set x := mapPt e.hom he (E.L.one t) with hx
  calc x = E'.L.mul t (E'.L.one t) x := (E'.L.one_mul t x).symm
    _ = E'.L.mul t (E'.L.mul t (E'.L.inv t x) x) x := by rw [E'.L.inv_mul_cancel]
    _ = E'.L.mul t (E'.L.inv t x) (E'.L.mul t x x) := E'.L.mul_assoc t _ _ _
    _ = E'.L.mul t (E'.L.inv t x) x := by rw [← h]
    _ = E'.L.one t := E'.L.inv_mul_cancel t x

theorem mapPt_nsmulPt (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N' S)
    (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    mapPt e.hom he (nsmulPt E.L t n P) = nsmulPt E'.L t n (mapPt e.hom he P) := by
  induction n with
  | zero => exact mapPt_one E E' e he hmul t
  | succ n ih =>
    show mapPt e.hom he (E.L.mul t (nsmulPt E.L t n P) P) =
      E'.L.mul t (nsmulPt E'.L t n (mapPt e.hom he P)) (mapPt e.hom he P)
    rw [hmul, ih]

end L2cBody

open L2cBody in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N N' : ℕ} {S : Type u} [CommRing S] {m : ℕ}
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N' S)
    (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x)
    (P : E.FullLevel m) :
    ∃ P' : E'.FullLevel m, P'.P = mapPt e.hom he P.P := by
  have he' : e.inv ≫ E.f = E'.f := by rw [← he, Iso.inv_hom_id_assoc]
  refine ⟨⟨mapPt e.hom he P.P, ?_, ?_, ?_⟩, rfl⟩
  · rw [← mapPt_nsmulPt E E' e he hmul, P.torsion, mapPt_one E E' e he hmul]
  · intro k _ _ sk Q' hQ'
    obtain ⟨x, hx⟩ := P.generates k sk (mapPt e.inv he' Q') (by
      apply mapPt_injective e he
      rw [mapPt_nsmulPt E E' e he hmul, mapPt_mapPt_inv, hQ', mapPt_one E E' e he hmul])
    refine ⟨x, ?_⟩
    rw [← mapPt_sectionAt, ← mapPt_pushPt e he (E.act x) (E.act_over x) (E'.act x) (E'.act_over x) (hact x),
      hx, mapPt_mapPt_inv]
  · intro k _ _ sk x
    rw [← P.annihilator k sk x, ← mapPt_sectionAt,
      ← mapPt_pushPt e he (E.act x) (E.act_over x) (E'.act x) (E'.act_over x) (hact x),
      ← mapPt_one E E' e he hmul (geomPoint k sk)]
    exact ⟨fun h => mapPt_injective e he h, fun h => by rw [h]⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt (solution)
