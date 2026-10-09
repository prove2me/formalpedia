-- Prove2me | solution 1 for BookProof.GaussCoordCombo.pderiv_aeval_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:42:03.271361+00:00
-- url     : https://prove2.me/submissions/ea9b4820-dab8-4e26-a959-71ab3801c33e

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.pderiv_aeval_self
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (f : Polynomial ℂ) :
    pderiv i (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) f)
      = Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) (Polynomial.derivative f) := by

  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp only [Polynomial.aeval_monomial, Polynomial.derivative_monomial, map_mul,
        algebraMap_eq]
      rw [MvPolynomial.pderiv_C_mul, Derivation.leibniz_pow, MvPolynomial.pderiv_X]
      simp [MvPolynomial.C_eq_smul_one]
