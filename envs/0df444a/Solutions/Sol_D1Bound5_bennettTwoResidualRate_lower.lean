-- Prove2me | solution 1 for D1Bound5.bennettTwoResidualRate_lower
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:40.776098+00:00
-- url     : https://prove2.me/submissions/67a8055b-80b7-4a39-a232-310c1591997f

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
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions

section
namespace D1Bound5

/-- The exact elementary comparison underlying the paper's lower bound
for the two-anchor exponential rate. -/
theorem bennett_two_rate_scalar_lower (T : ℝ) (hT : 1000 ≤ T) :
    128 * T ^ 2 < 135 * (T - 1) ^ 2 := by
  have hp := mul_nonneg (sub_nonneg.mpr hT) (show 0 ≤ T by linarith only [hT])
  nlinarith only [hT, hp]

/-- The actual residual rate exceeds the manuscript's simpler quadratic
rate. Only the triangle-inequality bound on the node separation is used. -/
theorem _root_.solution (A B C δ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hAB : A ≤ B) (hδAB : δ ≤ A + B) (hAC : 1000 ≤ A * C) :
    2 * A * C ^ 2 / (5 * B) < bennettTwoResidualRate A B C δ := by
  have hδle : δ ≤ 2 * B := by linarith only [hAB, hδAB]
  have hδsq : δ ^ 2 ≤ 4 * B ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hδle)
      (show 0 ≤ 2 * B + δ by positivity)
    nlinarith only [hp]
  have hden : 16 * A * δ ^ 2 ≤ 64 * A * B ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left hδsq (show 0 ≤ 16 * A by positivity)
    nlinarith only [hp]
  have hmin : 27 * B * (A * C - 1) ^ 2 / (64 * A * B ^ 2) ≤
      bennettTwoResidualRate A B C δ := by
    unfold bennettTwoResidualRate
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  apply lt_of_lt_of_le _ hmin
  apply (div_lt_div_iff₀ (show 0 < 5 * B by positivity)
    (show 0 < 64 * A * B ^ 2 by positivity)).mpr
  have hp := mul_lt_mul_of_pos_left (bennett_two_rate_scalar_lower (A * C) hAC)
    (show 0 < B ^ 2 by positivity)
  nlinarith only [hp]



end D1Bound5
end
