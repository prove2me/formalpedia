-- Prove2me | solution 1 for BookProof.GaussCoordCombo.gaussInt_hermiteFactor_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:43:34.816977+00:00
-- url     : https://prove2.me/submissions/07fc33bf-f767-43bb-99ed-b22a0db24a95

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.gaussInt_hermiteFactor_mul
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Theorems.Thm_BookProof_GaussCoordCombo_pderiv_hermiteFactor_self
import Theorems.Thm_BookProof_GaussCoordCombo_hermiteFactor_succ_eq
import Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_zero_prime
import Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_creation
import Definitions.Def_ChapterHermiteProductCore
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (m n : ℕ) {R : MvPolynomial (Fin d) ℂ}
    (hR : pderiv i R = 0) :
    gaussInt (hermiteFactor i m * (hermiteFactor i n * R))
      = (if m = n then (n.factorial : ℂ) else 0) * gaussInt R := by

  induction m generalizing n with
  | zero =>
      cases n with
      | zero => simp [hermiteFactor_zero]
      | succ k =>
          have hstep : gaussInt (hermiteFactor i (k + 1) * R)
              = gaussInt (hermiteFactor i k * pderiv i R) := by
            rw [hermiteFactor_succ_eq, gaussInt_creation]
          rw [hermiteFactor_zero, one_mul, hstep, hR, mul_zero, gaussInt_zero_prime]
          simp
  | succ m ih =>
      have hq : pderiv i (hermiteFactor i n * R) = pderiv i (hermiteFactor i n) * R := by
        rw [Derivation.leibniz, hR]
        simp [smul_eq_mul, mul_comm]
      have hstep : gaussInt (hermiteFactor i (m + 1) * (hermiteFactor i n * R))
          = gaussInt (hermiteFactor i m * (pderiv i (hermiteFactor i n) * R)) := by
        rw [hermiteFactor_succ_eq, gaussInt_creation, hq]
      cases n with
      | zero =>
          rw [hstep, hermiteFactor_zero]
          simp [gaussInt_zero_prime]
      | succ k =>
          rw [hstep, pderiv_hermiteFactor_self]
          simp only [smul_mul_assoc, mul_smul_comm, gaussInt_smul, ih k]
          by_cases h : m = k
          · subst h
            rw [if_pos rfl, if_pos rfl, Nat.factorial_succ]
            push_cast
            ring
          · rw [if_neg h, if_neg (by omega)]
            simp
