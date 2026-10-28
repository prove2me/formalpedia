-- Prove2me | solution 1 for D1Bound5.finiteUnequalClearedEntry_eq_scaled_residue
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:37:08.239705+00:00
-- url     : https://prove2.me/submissions/a970c008-4544-4c16-bf8c-9028c6098151

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
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteUnequalEntry_Definitions
import Definitions.Def_D1Bound5_UnequalPoleResidual_Definitions
import Theorems.Thm_D1Bound5_bennettResidueTaylor_homogenize
import Theorems.Thm_D1Bound5_finiteUnequalOrders_le

section
open Finset

namespace D1Bound5









variable {F : Type*} [Field F] [CharZero F]









theorem _root_.solution (x y c : F)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0)
    (k m : ℕ) (hmk : m ≤ k) (i j : Fin 3) :
    finiteUnequalClearedEntry x y c k m i j =
      (4^k*x^m*y^m*(x-y)^(2*k)*(x*y*c)^k)*
        (unequalPolePolynomial (bennettTwoNodes x y) (finiteUnequalOrders k m i)
          k (1/2 : F) j).eval (x*y*c)⁻¹ := by
  have hN : x*y*c ≠ 0 := mul_ne_zero (mul_ne_zero hx hy) hc
  unfold finiteUnequalClearedEntry unequalPolePolynomial
  rw [← bennettResidueTaylor_homogenize k (finiteUnequalOrders k m i j)
    (finiteUnequalOrders_le k m hmk i j) (1/2 : F) (bennettTwoNodes x y j)
    (x*y*c) (bennettLocalReciprocal (bennettTwoNodes x y) (finiteUnequalOrders k m i) j) hN]
  ring





end D1Bound5
end
