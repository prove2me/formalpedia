-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_cauchy_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:52:04.746191+00:00
-- url     : https://prove2.me/submissions/a81b1014-7826-4c15-bee2-3f176c76811a

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
import Theorems.Thm_D1Bound5_halfBinomialCoeff_hasSum_cpow

section
namespace D1Bound5



/-- The full Cauchy product of the two half-binomial series converges
absolutely to the product of their principal complex powers. -/
theorem _root_.solution (x y z : ℂ)
    (hx : ‖x * z‖ < 1) (hy : ‖y * z‖ < 1) :
    HasSum (fun n : ℕ => ∑ ij ∈ Finset.antidiagonal n,
      ((halfBinomialCoeff ij.1 : ℂ) * (x * z) ^ ij.1) *
      ((halfBinomialCoeff ij.2 : ℂ) * (y * z) ^ ij.2))
      (((1 + x * z) ^ (1 / 2 : ℂ)) * ((1 + y * z) ^ (1 / 2 : ℂ))) := by
  have hsx := halfBinomialCoeff_hasSum_cpow (x * z) hx
  have hsy := halfBinomialCoeff_hasSum_cpow (y * z) hy
  have hnx := hsx.summable.norm
  have hny := hsy.summable.norm
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hnx hny
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnx hny
  rw [hsx.tsum_eq, hsy.tsum_eq] at hprod
  rw [hprod]
  exact hs.of_norm.hasSum





end D1Bound5
end
