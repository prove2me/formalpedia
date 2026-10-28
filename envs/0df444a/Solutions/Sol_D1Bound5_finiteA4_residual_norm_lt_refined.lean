-- Prove2me | solution 1 for D1Bound5.finiteA4_residual_norm_lt_refined
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:22.329086+00:00
-- url     : https://prove2.me/submissions/716f3371-c263-4479-954b-5d988f8645c1

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
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA4Residual_Definitions
import Theorems.Thm_D1Bound5_finiteA4_residual_norm_lt_point

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The actual residual retains the evaluated anchor distance. The sole
extra comparison concerns explicit norms, and is verified by fixed-pair data. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖)
    (hdelta : ‖x‖ ≤ ‖x-y‖) (R : ℝ)
    (hR : (6363/409600 : ℝ)*‖x-y‖^8 ≤ R*‖y‖^8) (i : Fin 3) :
    ‖finiteA4Residual x y c i‖ < R*‖y‖^4/(‖x‖^5*‖c‖^7) := by
  have hX := norm_pos_iff.mpr hx
  have hY := norm_pos_iff.mpr hy
  have hC := norm_pos_iff.mpr hc
  have hrow : ‖x‖ ≤ ‖finiteA4RowFactor x y i‖ := by
    fin_cases i
    · simpa [finiteA4RowFactor] using hdelta
    · simp [finiteA4RowFactor]
    · simpa [finiteA4RowFactor] using hXY
  have hrowpos : 0 < ‖finiteA4RowFactor x y i‖ := hX.trans_le hrow
  have hcoef : (6363/409600 : ℝ)*‖x-y‖^8/‖y‖^8 ≤ R :=
    (div_le_iff₀ (by positivity)).mpr hR
  apply (finiteA4_residual_norm_lt_point x y c hx hy hc hxy hXY hXC i).trans_le
  calc
    _ = ((6363/409600 : ℝ)*‖x-y‖^8/(‖x‖^4*‖y‖^4*‖c‖^7))/
        ‖finiteA4RowFactor x y i‖ := by ring
    _ ≤ ((6363/409600 : ℝ)*‖x-y‖^8/(‖x‖^4*‖y‖^4*‖c‖^7))/‖x‖ := by
      apply div_le_div_of_nonneg_left (by positivity) hX hrow
    _ = ((6363/409600 : ℝ)*‖x-y‖^8/‖y‖^8)*
        (‖y‖^4/(‖x‖^5*‖c‖^7)) := by
      field_simp [hX.ne',hY.ne',hC.ne']
      <;> ring
    _ ≤ R*(‖y‖^4/(‖x‖^5*‖c‖^7)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring








end D1Bound5
end
