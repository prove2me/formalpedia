-- Prove2me | solution 1 for D1Bound5.unequalPolePolynomial_residual_coeff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:23:25.432421+00:00
-- url     : https://prove2.me/submissions/9d244be1-7e0e-4690-b8af-7e204b17210f

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
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Definitions.Def_D1Bound5_UnequalPoleResidual_Definitions
import Theorems.Thm_D1Bound5_bennettResidueTaylor_coeff_mul_binomial

section
open Finset

namespace D1Bound5

variable {I : Type*} [Fintype I] [DecidableEq I]





theorem _root_.solution
    {F : Type*} [Field F] [CharZero F]
    (a : I → F) (e : I → ℕ) (k : ℕ) (he : ∀ j, e j ≤ k)
    (ν : F) (r : ℕ) :
    PowerSeries.coeff r
      (∑ j, (unequalPolePolynomial a e k ν j : PowerSeries F)*
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) =
      Ring.choose ((k : F)+ν) r *
        ∑ j, bennettLocalResidue a e (Polynomial.X^r) j := by
  rw [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold unequalPolePolynomial
  rw [bennettResidueTaylor_coeff_mul_binomial k (e j) r (he j)]
  simp [bennettLocalResidue,bennettShiftToSeries]







end D1Bound5
end
