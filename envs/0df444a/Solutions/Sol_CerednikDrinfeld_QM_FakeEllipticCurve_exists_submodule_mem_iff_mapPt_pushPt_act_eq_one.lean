-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_submodule_mem_iff_mapPt_pushPt_act_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ced22c5d-bae3-5c13-9524-cf881f1d258d

import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_mem_iff_mapPt_pushPt_act_eq_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion
open QuaternionAlgebra

namespace AnnIdeal

variable {S : Type u} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem eq_one_of_eq_mul_self (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t E.f) (hx : x = E.L.mul t x x) : x = E.L.one t := by
  have := congrArg (fun y => E.L.mul t (E.L.inv t x) y) hx
  rw [E.L.inv_mul_cancel, ← E.L.mul_assoc, E.L.inv_mul_cancel, E.L.one_mul] at this
  exact this.symm

theorem pushPt_act_one (E : FakeEllipticCurve Λ N S) (m : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt (E.act m) (E.act_over m) (E.L.one t) = E.L.one t := by
  have h := E.act_hom m t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  exact eq_one_of_eq_mul_self E t _ h

theorem mapPt_one (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    mapPt φ hφ (E.L.one t) = E'.L.one t := by
  have h := hφmul t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  exact eq_one_of_eq_mul_self E' t _ h

theorem mapPt_pushPt_act (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) (m : ↥Λ)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f) :
    mapPt φ hφ (pushPt (E.act m) (E.act_over m) P) = pushPt (E'.act m) (E'.act_over m) (mapPt φ hφ P) := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc, hφact m]

theorem pushPt_act_mul (E : FakeEllipticCurve Λ N S) (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩) (E.act_over _) P =
      pushPt (E.act x) (E.act_over x) (pushPt (E.act y) (E.act_over y) P) := by
  apply Subtype.ext
  simp only [mapPt_coe, E.act_mul x y h, Category.assoc]

theorem pushPt_act_zero (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t E.f) : pushPt (E.act 0) (E.act_over 0) P = E.L.one t := by
  have h := E.act_add 0 0 t P
  rw [add_zero] at h
  exact eq_one_of_eq_mul_self E t _ h

end AnnIdeal

open AnnIdeal in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N : ℕ}
    {S : Type u} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x)
    (r : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P₀ : SchemeHomOver t E.f)
    (hP₀ : nsmulPt E.L t r P₀ = E.L.one t) :
    ∃ J : Submodule ℤ ℍ[ℚ, a, b],
      (∀ x, x ∈ J ↔ ∃ hx : x ∈ Λ, mapPt φ hφ (pushPt (E.act ⟨x, hx⟩) (E.act_over _) P₀) = E'.L.one t) ∧
      J ≤ Λ ∧ (∀ y ∈ Λ, (r : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) := by
  classical

  have hsub : ∀ (x y : ↥Λ) (hx : (x : ℍ[ℚ, a, b]) ∈ Λ), (⟨(x : ℍ[ℚ, a, b]), hx⟩ : ↥Λ) = x := fun x y hx => rfl
  let J₀ : AddSubgroup ℍ[ℚ, a, b] :=
    { carrier := {x | ∃ hx : x ∈ Λ, mapPt φ hφ (pushPt (E.act ⟨x, hx⟩) (E.act_over _) P₀) = E'.L.one t}
      add_mem' := by
        rintro x y ⟨hx, hxJ⟩ ⟨hy, hyJ⟩
        refine ⟨Λ.add_mem hx hy, ?_⟩
        have : (⟨x + y, Λ.add_mem hx hy⟩ : ↥Λ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
        rw [this, E.act_add, hφmul, hxJ, hyJ, E'.L.one_mul]
      zero_mem' := by
        refine ⟨Λ.zero_mem, ?_⟩
        have : (⟨0, Λ.zero_mem⟩ : ↥Λ) = 0 := rfl
        rw [this, pushPt_act_zero, mapPt_one E E' φ hφ hφmul]
      neg_mem' := by
        rintro x ⟨hx, hxJ⟩
        refine ⟨Λ.neg_mem hx, ?_⟩
        have hneg : (⟨-x, Λ.neg_mem hx⟩ : ↥Λ) = -⟨x, hx⟩ := rfl
        have h0 := E.act_add (-⟨x, hx⟩) ⟨x, hx⟩ t P₀
        rw [neg_add_cancel, pushPt_act_zero] at h0

        have h1 := congrArg (mapPt φ hφ) h0
        rw [hφmul, hxJ, E'.L.mul_one, mapPt_one E E' φ hφ hφmul] at h1
        rw [hneg]; exact h1.symm }
  refine ⟨AddSubgroup.toIntSubmodule J₀, fun x => Iff.rfl, fun x hx => hx.1, ?_, ?_⟩
  · intro y hy
    have hr1 : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
      have : ((r : ℚ) : ℍ[ℚ, a, b]) = (r : ℤ) • (1 : ℍ[ℚ, a, b]) := by
        rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, Algebra.smul_def, mul_one]; rfl
      rw [this]; exact Λ.smul_mem _ hΛ.one_mem
    have hyr : y * ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem hy hr1
    have heq : (r : ℤ) • y = y * ((r : ℚ) : ℍ[ℚ, a, b]) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, QuaternionAlgebra.mul_coe_eq_smul]
    refine ⟨by rw [heq]; exact hyr, ?_⟩
    have : (⟨(r : ℤ) • y, by rw [heq]; exact hyr⟩ : ↥Λ) = ⟨(⟨y, hy⟩ : ↥Λ) * ((⟨((r : ℚ) : ℍ[ℚ, a, b]), hr1⟩ : ↥Λ) : ℍ[ℚ, a, b]), hyr⟩ :=
      Subtype.ext heq
    rw [this, pushPt_act_mul E ⟨y, hy⟩ ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr1⟩ hyr,
      CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hΛ.one_mem r hr1 t P₀, hP₀,
      pushPt_act_one, mapPt_one E E' φ hφ hφmul]
  · rintro m hm x ⟨hx, hxJ⟩
    refine ⟨hΛ.mul_mem hm hx, ?_⟩
    have : (⟨m * x, hΛ.mul_mem hm hx⟩ : ↥Λ) = ⟨((⟨m, hm⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨x, hx⟩ : ↥Λ) : ℍ[ℚ, a, b]), hΛ.mul_mem hm hx⟩ := rfl
    rw [this, pushPt_act_mul E ⟨m, hm⟩ ⟨x, hx⟩, mapPt_pushPt_act E E' φ hφ hφact, hxJ, pushPt_act_one]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_mem_iff_mapPt_pushPt_act_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_mem_iff_mapPt_pushPt_act_eq_one (solution)
