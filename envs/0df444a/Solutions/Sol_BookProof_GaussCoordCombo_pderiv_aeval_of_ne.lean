-- Prove2me | solution 1 for BookProof.GaussCoordCombo.pderiv_aeval_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:42:04.259854+00:00
-- url     : https://prove2.me/submissions/f9fc21ea-86aa-440c-b821-db67fbcabe3c

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.pderiv_aeval_of_ne
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {i j : Fin d} (h : j ≠ i) (f : Polynomial ℂ) :
    pderiv j (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) f) = 0 := by

  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp only [Polynomial.aeval_monomial, algebraMap_eq]
      rw [MvPolynomial.pderiv_C_mul, Derivation.leibniz_pow, MvPolynomial.pderiv_X,
        Pi.single_apply, if_neg (Ne.symm h)]
      simp
