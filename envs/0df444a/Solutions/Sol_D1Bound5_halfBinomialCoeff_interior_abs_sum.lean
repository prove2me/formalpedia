-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_interior_abs_sum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:28:58.560534+00:00
-- url     : https://prove2.me/submissions/a60bf006-a57b-4b84-a9c1-a4d2fce1f027

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_interior_convolution
import Theorems.Thm_D1Bound5_halfBinomialCoeff_pair_abs_signed
import Theorems.Thm_D1Bound5_halfBinomialCoeff_signed_nonneg

section
open Finset

namespace D1Bound5



/-- The sign of a positive-degree coefficient describes its absolute value. -/
theorem halfBinomialCoeff_abs_signed (k : ℕ) :
    |halfBinomialCoeff (k + 1)| =
      (-1 : ℝ) ^ k * halfBinomialCoeff (k + 1) := by
  calc
    |halfBinomialCoeff (k + 1)| =
        |(-1 : ℝ) ^ k * halfBinomialCoeff (k + 1)| := by
          simp [abs_mul]
    _ = _ := abs_of_nonneg (halfBinomialCoeff_signed_nonneg k)



/-- The interior absolute convolution is exactly twice the endpoint modulus. -/
theorem _root_.solution (k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
      |halfBinomialCoeff (ij.1 + 1) * halfBinomialCoeff (ij.2 + 1)|) =
        2 * |halfBinomialCoeff (k + 2)| := by
  calc
    (∑ ij ∈ Finset.antidiagonal k,
      |halfBinomialCoeff (ij.1 + 1) * halfBinomialCoeff (ij.2 + 1)|) =
        (∑ ij ∈ Finset.antidiagonal k,
          (-1 : ℝ) ^ (k + 2) *
            (halfBinomialCoeff (ij.1 + 1) * halfBinomialCoeff (ij.2 + 1))) := by
          apply Finset.sum_congr rfl
          intro ij hij
          rw [halfBinomialCoeff_pair_abs_signed]
          have hsum : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
          rw [hsum]
    _ = (-1 : ℝ) ^ (k + 2) *
          (∑ ij ∈ Finset.antidiagonal k,
            halfBinomialCoeff (ij.1 + 1) * halfBinomialCoeff (ij.2 + 1)) := by
          rw [Finset.mul_sum]
    _ = 2 * |halfBinomialCoeff (k + 2)| := by
          rw [halfBinomialCoeff_interior_convolution,
              halfBinomialCoeff_abs_signed (k + 1)]
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring



end D1Bound5
end
