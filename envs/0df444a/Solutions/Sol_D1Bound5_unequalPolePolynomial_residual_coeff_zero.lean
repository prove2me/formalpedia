-- Prove2me | solution 1 for D1Bound5.unequalPolePolynomial_residual_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:23:26.224701+00:00
-- url     : https://prove2.me/submissions/79b771b8-eaa3-4ad6-961d-3c34e809e087

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_UnequalPoleResidual_Definitions
import Theorems.Thm_D1Bound5_bennettLocalResidue_sum_eq_zero
import Theorems.Thm_D1Bound5_unequalPolePolynomial_residual_coeff

section
open Finset

namespace D1Bound5

variable {I : Type*} [Fintype I] [DecidableEq I]







/-- Exact cancellation through one less than the total pole order. -/
theorem _root_.solution
    {F : Type*} [Field F] [CharZero F]
    (a : I → F) (ha : Function.Injective a) (e : I → ℕ)
    (k : ℕ) (he : ∀ j, e j ≤ k) (ν : F)
    (r : ℕ) (hr : r < (∑ j, (e j+1))-1) :
    PowerSeries.coeff r
      (∑ j, (unequalPolePolynomial a e k ν j : PowerSeries F)*
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) = 0 := by
  rw [unequalPolePolynomial_residual_coeff a e k he ν r]
  have hdeg : (Polynomial.X^r : Polynomial F).degree <
      ((∑ j, (e j+1))-1 : ℕ) := by
    rw [Polynomial.degree_X_pow]
    exact WithBot.coe_lt_coe.mpr hr
  rw [bennettLocalResidue_sum_eq_zero a ha e (Polynomial.X^r) hdeg,mul_zero]





end D1Bound5
end
