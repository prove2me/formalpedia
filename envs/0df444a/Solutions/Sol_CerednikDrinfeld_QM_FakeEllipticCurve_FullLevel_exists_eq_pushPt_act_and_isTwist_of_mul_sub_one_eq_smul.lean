-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2fb937f0-1fc4-5f46-aeea-48254d941eac

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

universe u

namespace TwistClosedBody

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem pushPt_act_one (E : FakeEllipticCurve Λ N S) (x : ↥Λ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt (E.act x) (E.act_over x) (E.L.one t) = E.L.one t := by
  letI := E.L.pointGroup t
  have h := E.act_hom x t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h

  exact mul_left_cancel (a := pushPt (E.act x) (E.act_over x) (E.L.one t)) (h.symm.trans (mul_one _).symm)

theorem pushPt_act_nsmulPt (E : FakeEllipticCurve Λ N S) (x : ↥Λ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (Q : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (nsmulPt E.L t n Q) = nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) Q) := by
  induction n with
  | zero => exact pushPt_act_one E x t
  | succ n ih =>
      show pushPt (E.act x) (E.act_over x) (E.L.mul t (nsmulPt E.L t n Q) Q) =
        E.L.mul t (nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) Q)) (pushPt (E.act x) (E.act_over x) Q)
      rw [E.act_hom, ih]

theorem pushPt_act_pushPt_act (E : FakeEllipticCurve Λ N S) (x c : ↥Λ)
    (h : (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) ∈ Λ) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (pushPt (E.act c) (E.act_over c) Q) =
      pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]), h⟩) (E.act_over _) Q := by
  apply Subtype.ext
  simp only [pushPt, mapPt_coe, E.act_mul x c h, Category.assoc]

theorem sectionAt_pushPt_act (E : FakeEllipticCurve Λ N S) (c : ↥Λ)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) (k : Type u) [Field k] (sk : S →+* k) :
    FakeEllipticCurve.sectionAt (pushPt (E.act c) (E.act_over c) P) k sk =
      pushPt (E.act c) (E.act_over c) (FakeEllipticCurve.sectionAt P k sk) := by
  apply Subtype.ext
  simp only [FakeEllipticCurve.sectionAt, pushPt, mapPt_coe, schemeHomOverComp_coe, Category.assoc]

theorem pushPt_act_sectionAt_eq_of_sub_eq_smul (E : FakeEllipticCurve Λ N S) {m : ℕ} (P : E.FullLevel m)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (x x' y : ↥Λ)
    (h : (x : ℍ[ℚ, a, b]) - (x' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P.P k sk) =
      pushPt (E.act x') (E.act_over x') (FakeEllipticCurve.sectionAt P.P k sk) := by
  have hx : x = x' + (x - x') := by abel
  have hz : pushPt (E.act (x - x')) (E.act_over (x - x')) (FakeEllipticCurve.sectionAt P.P k sk) =
      E.L.one (geomPoint k sk) :=
    (P.annihilator k sk (x - x')).mpr ⟨y, by rw [← h]; rfl⟩
  rw [hx, E.act_add x' (x - x') (geomPoint k sk) (FakeEllipticCurve.sectionAt P.P k sk), hz, E.L.mul_one]

end TwistClosedBody

open TwistClosedBody in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ}
    {S : Type u} [CommRing S] {m : ℕ} (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m) (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ P' : E.FullLevel m, P'.P = pushPt (E.act c) (E.act_over c) P.P ∧
      FakeEllipticCurve.WithFullLevel.IsTwist c (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m S) ⟨E, P'⟩ := by

  have hmul : ∀ u v : ↥Λ, (u : ℍ[ℚ, a, b]) * (v : ℍ[ℚ, a, b]) ∈ Λ := fun u v => hΛ.mul_mem u.2 v.2
  obtain ⟨w, hw⟩ := hcd
  obtain ⟨w', hw'⟩ := hdc

  let cP : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f := pushPt (E.act c) (E.act_over c) P.P
  refine ⟨{ P := cP, torsion := ?_, generates := ?_, annihilator := ?_ }, rfl, ?_⟩
  ·
    show nsmulPt E.L (𝟙 _) m (pushPt (E.act c) (E.act_over c) P.P) = E.L.one _
    rw [← pushPt_act_nsmulPt, P.torsion, pushPt_act_one]
  ·
    intro k _ _ sk Q hQ
    obtain ⟨x, hx⟩ := P.generates k sk Q hQ
    refine ⟨⟨(x : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]), hmul x d⟩, ?_⟩
    rw [sectionAt_pushPt_act, pushPt_act_pushPt_act E _ c (hmul _ c), ← hx]
    refine pushPt_act_sectionAt_eq_of_sub_eq_smul E P k sk _ x ⟨(x : ℍ[ℚ, a, b]) * (w' : ℍ[ℚ, a, b]), hmul x w'⟩ ?_

    show (x : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) =
      (m : ℚ) • ((x : ℍ[ℚ, a, b]) * (w' : ℍ[ℚ, a, b]))
    rw [← mul_smul_comm, ← hw']
    noncomm_ring
  ·
    intro k _ _ sk x
    rw [sectionAt_pushPt_act, pushPt_act_pushPt_act E x c (hmul x c), P.annihilator k sk]
    constructor
    · rintro ⟨y, hy⟩

      refine ⟨⟨(y : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]),
        Λ.sub_mem (hmul y d) (hmul x w)⟩, ?_⟩
      have hy' : (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := hy
      show (x : ℍ[ℚ, a, b]) = (m : ℚ) • ((y : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]))
      have key : (x : ℍ[ℚ, a, b]) =
          (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) -
            (x : ℍ[ℚ, a, b]) * ((c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1) := by
        noncomm_ring
      calc (x : ℍ[ℚ, a, b])
          = (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) -
              (x : ℍ[ℚ, a, b]) * ((c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1) := key
        _ = ((m : ℚ) • (y : ℍ[ℚ, a, b])) * (d : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) * ((m : ℚ) • (w : ℍ[ℚ, a, b])) := by
          rw [hy', hw]
        _ = (m : ℚ) • ((y : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b])) := by
          rw [smul_sub, smul_mul_assoc, mul_smul_comm]
    · rintro ⟨y, hy⟩
      refine ⟨⟨(y : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]), hmul y c⟩, ?_⟩
      have hy' : (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := hy
      show (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) = (m : ℚ) • ((y : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]))
      rw [hy', smul_mul_assoc]
  ·
    refine ⟨Iso.refl E.A, Category.id_comp E.f, ?_, ?_, ?_, ?_⟩
    · intro T t Q R
      have h : ∀ X : SchemeHomOver t E.f, mapPt (Iso.refl E.A).hom (Category.id_comp E.f) X = X :=
        fun X => Subtype.ext (Category.comp_id X.1)
      rw [h, h, h]
    · intro x
      show E.act x ≫ 𝟙 E.A = 𝟙 E.A ≫ E.act x
      rw [Category.comp_id, Category.id_comp]
    · intro T t Q
      have h : mapPt (Iso.refl E.A).hom (Category.id_comp E.f) Q = Q := Subtype.ext (Category.comp_id Q.1)
      rw [h]
    · exact Subtype.ext (Category.comp_id _)

end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul (solution)
