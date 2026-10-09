-- Prove2me | solution 1 for BookProof.GaussCoordCombo.hermiteFactor_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:42:30.694986+00:00
-- url     : https://prove2.me/submissions/2ef5a08c-7fae-4d43-8250-c9720a2cb6d6

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.hermiteFactor_succ_eq
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (n : ℕ) :
    hermiteFactor i (n + 1) = X i * hermiteFactor i n - pderiv i (hermiteFactor i n) := by

  have h : hermiteCx (n + 1) = Polynomial.X * hermiteCx n
      - Polynomial.derivative (hermiteCx n) := by
    simp [hermiteCx, Polynomial.derivative_map, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.hermite_succ]
  rw [hermiteFactor, h]
  simp [hermiteFactor]
