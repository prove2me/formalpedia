-- Prove2me | solution 1 for D1Bound5.bennettTwoResidualRate_pos
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:30:22.305823+00:00
-- url     : https://prove2.me/submissions/f0f0b68e-eba4-43a2-9f14-53931a6a37a2

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





theorem _root_.solution (A B C δ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ) (hAC : 1 < A * C) :
    0 < bennettTwoResidualRate A B C δ := by
  unfold bennettTwoResidualRate
  exact div_pos
    (mul_pos (mul_pos (by norm_num) hB) (sq_pos_of_pos (sub_pos.mpr hAC)))
    (mul_pos (mul_pos (by norm_num) hA) (sq_pos_of_pos hδ))







end D1Bound5
end
