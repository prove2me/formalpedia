-- Prove2me | solution 1 for EastinKnill.Transversal.infinitesimal_logical
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T20:53:19.296516+00:00
-- url     : https://prove2.me/submissions/b0cbfb88-a660-47eb-98c5-3d373ea35217

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix
open EastinKnill.Transversal

theorem solution {n : Type*} [Fintype n] [DecidableEq n] (P D : Matrix n n ℂ)
    (hD : D.IsHermitian)
    (h : ∀ ε : ℝ, IsLogical P (NormedSpace.exp (((ε : ℂ) * Complex.I) • D))) :
    (1 - P) * D * P = 0 := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  set A : Matrix n n ℂ := Complex.I • D with hA
  have hfun : (fun t : ℝ => (1 - P) * NormedSpace.exp (t • A) * P) = fun _ => 0 := by
    funext t
    have := h t
    unfold IsLogical at this
    have e : t • (Complex.I • D) = ((t:ℂ) * Complex.I) • D := by
      rw [← smul_assoc, Complex.real_smul]
    rw [hA, e]
    exact this
  have hd : HasDerivAt (fun t : ℝ => (1 - P) * NormedSpace.exp (t • A) * P)
      ((1 - P) * (NormedSpace.exp ((0:ℝ) • A) * A) * P) 0 :=
    ((hasDerivAt_exp_smul_const A (0:ℝ)).const_mul (1 - P)).mul_const P
  rw [hfun] at hd
  have h0 := hd.unique (hasDerivAt_const (0:ℝ) (0 : Matrix n n ℂ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h0
  have : Complex.I • ((1 - P) * D * P) = 0 := by
    rw [← h0, hA, Matrix.mul_smul, Matrix.smul_mul]
  exact (smul_eq_zero.mp this).resolve_left Complex.I_ne_zero
