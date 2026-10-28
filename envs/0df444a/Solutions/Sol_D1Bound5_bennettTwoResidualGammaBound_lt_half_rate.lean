-- Prove2me | solution 1 for D1Bound5.bennettTwoResidualGammaBound_lt_half_rate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:39.714849+00:00
-- url     : https://prove2.me/submissions/d6aa9d1d-cb29-42d1-89f2-3af6b31322b4

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoBetaBound_Definitions
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions
import Theorems.Thm_D1Bound5_bennettTwoBetaFactor_sqrt_mul_lt_half
import Theorems.Thm_D1Bound5_bennettTwoResidualGammaBound_mul_rate
import Theorems.Thm_D1Bound5_bennettTwoResidualRate_pos

section
namespace D1Bound5









theorem _root_.solution
    (A B C δ : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hδ : 0 < δ) (hAC : 1 < A * C) (k : ℕ) (hk : 1 ≤ k) :
    bennettTwoResidualGammaBound A B C δ k <
      1 / (2 * (bennettTwoResidualRate A B C δ) ^ k) := by
  have hR := bennettTwoResidualRate_pos A B C δ hA hB hδ hAC
  have hη : 0 < 1 - 1 / (A * C) := by
    have hdiv := (div_lt_one (mul_pos hA hC)).mpr hAC
    linarith
  have hη1 : 1 - 1 / (A * C) ≤ 1 :=
    sub_le_self _ (div_nonneg (by norm_num) (mul_pos hA hC).le)
  have hbound := bennettTwoBetaFactor_sqrt_mul_lt_half
    (1 - 1 / (A * C)) hη.le hη1 k hk
  rw [← bennettTwoResidualGammaBound_mul_rate A B C δ hA hB hC hδ hAC k] at hbound
  have hdiv : bennettTwoResidualGammaBound A B C δ k <
      (1 / 2 : ℝ) / (bennettTwoResidualRate A B C δ) ^ k :=
    (lt_div_iff₀ (pow_pos hR k)).mpr hbound
  simpa only [div_div, mul_comm] using hdiv



end D1Bound5
end
