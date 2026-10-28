-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_pair_abs_signed
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:11.961781+00:00
-- url     : https://prove2.me/submissions/0df0b7dc-d48e-41ef-b37e-7e8887b380d7

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_signed_pair_nonneg

section
open Finset

namespace D1Bound5





/-- All products of positive-degree coefficients have the prescribed sign. -/
theorem _root_.solution (i j : ℕ) :
    |halfBinomialCoeff (i + 1) * halfBinomialCoeff (j + 1)| =
       (-1 : ℝ) ^ (i + j + 2) *
         (halfBinomialCoeff (i + 1) * halfBinomialCoeff (j + 1)) := by
  calc
    |halfBinomialCoeff (i + 1) * halfBinomialCoeff (j + 1)| =
      |(-1 : ℝ) ^ (i + j + 2) *
          (halfBinomialCoeff (i + 1) * halfBinomialCoeff (j + 1))| := by
            simp [abs_mul]
    _ = _ := abs_of_nonneg (halfBinomialCoeff_signed_pair_nonneg i j)





end D1Bound5
end
