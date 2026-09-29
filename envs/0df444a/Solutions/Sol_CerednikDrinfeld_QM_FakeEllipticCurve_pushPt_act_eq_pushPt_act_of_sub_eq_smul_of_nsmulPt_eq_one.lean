-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_eq_pushPt_act_of_sub_eq_smul_of_nsmulPt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d00d8a03-fcbd-5afb-8386-88be87acce4e

import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_eq_pushPt_act_of_sub_eq_smul_of_nsmulPt_eq_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (m : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t m P = E.L.one t)
    (c c' : ↥Λ) (hcc' : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) - (c' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    pushPt (E.act c) (E.act_over c) P = pushPt (E.act c') (E.act_over c') P := by
  obtain ⟨y, hy⟩ := hcc'

  have hm : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have e1 : ((m : ℚ) : ℍ[ℚ, a, b]) = m • (1 : ℍ[ℚ, a, b]) := by
      rw [nsmul_eq_mul, mul_one]; norm_cast
    rw [e1]; exact nsmul_mem h1 m

  have hmy_eq : ((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
    rw [Algebra.smul_def, map_natCast]; norm_cast
  have hmy : ((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [hmy_eq, Nat.cast_smul_eq_nsmul]; exact nsmul_mem y.2 m
  have hc₀ : (c : ℍ[ℚ, a, b]) = (c' : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) := by
    rw [hmy_eq]
    rw [← hy]
    abel
  have hc : c = c' + ⟨((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hmy⟩ :=
    Subtype.ext hc₀
  subst hc

  have hone : ∀ (x : ↥Λ), pushPt (E.act x) (E.act_over x) (E.L.one t) = E.L.one t := by
    intro x
    have h := E.act_hom x t (E.L.one t) (E.L.one t)
    rw [E.L.one_mul] at h
    set p := pushPt (E.act x) (E.act_over x) (E.L.one t)
    calc p = E.L.mul t (E.L.mul t (E.L.inv t p) p) p := by rw [E.L.inv_mul_cancel, E.L.one_mul]
      _ = E.L.mul t (E.L.inv t p) (E.L.mul t p p) := by rw [E.L.mul_assoc]
      _ = E.L.mul t (E.L.inv t p) p := by rw [← h]
      _ = E.L.one t := E.L.inv_mul_cancel t p
  have hcomm : ∀ (k : ℕ) (Q : SchemeHomOver t E.f),
      nsmulPt E.L t k (pushPt (E.act y) (E.act_over y) Q) = pushPt (E.act y) (E.act_over y) (nsmulPt E.L t k Q) := by
    intro k Q
    induction k with
    | zero => simp only [nsmulPt, hone]
    | succ k ih => simp only [nsmulPt, ih, E.act_hom]
  have hz_act : E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hmy⟩ = E.act y ≫ E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ :=
    E.act_mul ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ y hmy
  have hzP : pushPt (E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hmy⟩) (E.act_over _) P = E.L.one t := by
    have : pushPt (E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hmy⟩) (E.act_over _) P
        = pushPt (E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩) (E.act_over _) (pushPt (E.act y) (E.act_over y) P) := by
      apply Subtype.ext
      simp only [mapPt_coe, hz_act, Category.assoc]
    rw [this, pushPt_act_natCast_eq_nsmulPt E h1 m hm, hcomm, hP, hone]
  rw [E.act_add, hzP, E.L.mul_one]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_eq_pushPt_act_of_sub_eq_smul_of_nsmulPt_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_eq_pushPt_act_of_sub_eq_smul_of_nsmulPt_eq_one (solution)
