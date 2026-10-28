-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_signed_pair_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:35:14.323608+00:00
-- url     : https://prove2.me/submissions/20104165-99e6-479f-b311-13d2c5ff4138

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_signed_nonneg

section
open Finset

namespace D1Bound5













/-- Every interior product has the sign needed for the sharp convolution bound. -/
theorem _root_.solution (i j : ℕ) :
    0 ≤ (-1 : ℝ) ^ (i + j + 2) *
      (halfBinomialCoeff (i + 1) * halfBinomialCoeff (j + 1)) := by
  have hi := halfBinomialCoeff_signed_nonneg i
  have hj := halfBinomialCoeff_signed_nonneg j
  have hpow : (-1 : ℝ) ^ (i + j + 2) =
      (-1 : ℝ) ^ i * (-1 : ℝ) ^ j := by
    simp [pow_add]
  rw [hpow]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using (mul_nonneg hi hj)



end D1Bound5
end
