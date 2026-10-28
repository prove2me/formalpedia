-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_weighted_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:54.616408+00:00
-- url     : https://prove2.me/submissions/1f4491fc-b756-42a0-abdf-a9d435fc82fc

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_cauchy_hasSum
import Theorems.Thm_D1Bound5_halfBinomialCoeff_cauchy_rearrange

section
namespace D1Bound5







/-- Exact convergence of the weighted two-variable half-binomial series
to the corresponding product of complex square-root powers. -/
theorem _root_.solution (x y z : ℂ)
    (hx : ‖x * z‖ < 1) (hy : ‖y * z‖ < 1) :
    HasSum (fun n : ℕ =>
      (∑ ij ∈ Finset.antidiagonal n,
        ((halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2 : ℝ) : ℂ) *
          x ^ ij.1 * y ^ ij.2) * z ^ n)
      (((1 + x * z) ^ (1 / 2 : ℂ)) * ((1 + y * z) ^ (1 / 2 : ℂ))) := by
  convert halfBinomialCoeff_cauchy_hasSum x y z hx hy using 1
  ext n
  exact (halfBinomialCoeff_cauchy_rearrange x y z n).symm

end D1Bound5
end
