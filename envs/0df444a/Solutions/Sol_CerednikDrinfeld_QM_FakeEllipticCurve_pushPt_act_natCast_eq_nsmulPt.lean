-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/8087e84c-ed6c-5ae5-b220-c41d49ba33d4

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩) (E.act_over _) P = nsmulPt E.L t n P := by

  have hmem : ∀ m : ℕ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    intro m
    have : ((m : ℚ) : ℍ[ℚ, a, b]) = (m : ℤ) • (1 : ℍ[ℚ, a, b]) := by
      rw [zsmul_eq_mul, Int.cast_natCast, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ h1

  have key : ∀ m : ℕ, pushPt (E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hmem m⟩) (E.act_over _) P = nsmulPt E.L t m P := by
    intro m
    induction m with
    | zero =>

      have h0 : (⟨((0 : ℕ) : ℚ), hmem 0⟩ : ↥Λ) = ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hmem 0⟩ + ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hmem 0⟩ := by
        apply Subtype.ext; push_cast; simp
      have h := E.act_add ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hmem 0⟩ ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hmem 0⟩ t P
      rw [← h0] at h
      letI := E.L.pointGroup t
      have h' : pushPt (E.act ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hmem 0⟩) (E.act_over _) P *
          pushPt (E.act ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hmem 0⟩) (E.act_over _) P =
          pushPt (E.act ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hmem 0⟩) (E.act_over _) P := h.symm
      exact mul_eq_left.mp h'
    | succ m ih =>
      have hs : (⟨(((m + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hmem (m + 1)⟩ : ↥Λ) =
          ⟨((m : ℚ) : ℍ[ℚ, a, b]), hmem m⟩ + ⟨(1 : ℍ[ℚ, a, b]), h1⟩ := by
        apply Subtype.ext; push_cast; rfl
      rw [hs, E.act_add, ih]
      show E.L.mul t (nsmulPt E.L t m P) (pushPt (E.act ⟨1, h1⟩) (E.act_over _) P) = E.L.mul t (nsmulPt E.L t m P) P
      congr 1
      apply Subtype.ext
      show P.1 ≫ E.act ⟨1, h1⟩ = P.1
      rw [E.act_one h1, Category.comp_id]
  exact key n

end S_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt (solution)
