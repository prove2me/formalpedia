-- Prove2me | solution 1 for D1Bound5.finiteA3_residual_norm_lt_max_distance
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:12.510843+00:00
-- url     : https://prove2.me/submissions/9fa04b96-5209-4c25-81b5-77e0e6db2ebf

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
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA3Residual_Definitions
import Theorems.Thm_D1Bound5_finiteA3RowFactor_ne_zero
import Theorems.Thm_D1Bound5_finiteA3_residual_norm_lt_point

section
open scoped NumberField
open Module

namespace D1Bound5

/-- Actual A3 residual without any separation assumption between A
and |a-b|. The maximum preserves all three distinct row factors. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (R : ℝ)
    (hR : (707/40960 : ℝ)*max (‖x-y‖^6) (‖x‖*‖x-y‖^5) ≤ R*‖y‖^6)
    (i : Fin 3) :
    ‖finiteA3Residual x y c i‖ < R*‖y‖^3/(‖x‖^4*‖c‖^5) := by
  have hX := norm_pos_iff.mpr hx
  have hY := norm_pos_iff.mpr hy
  have hC := norm_pos_iff.mpr hc
  have hD := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hrowpos := norm_pos_iff.mpr (finiteA3RowFactor_ne_zero x y hx hy hxy i)
  let V := max (‖x-y‖^6) (‖x‖*‖x-y‖^5)
  have hleft : ‖x-y‖^6 ≤ V := le_max_left _ _
  have hright : ‖x‖*‖x-y‖^5 ≤ V := le_max_right _ _
  have hV : 0 ≤ V := (pow_nonneg hD.le 6).trans hleft
  have hrow : ‖x‖*‖x-y‖^6 ≤ V*‖finiteA3RowFactor x y i‖ := by
    fin_cases i
    · change ‖x‖*‖x-y‖^6 ≤ V*‖x-y‖
      rw [pow_succ (‖x-y‖) 5, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hright hD.le
    · have hh := mul_le_mul_of_nonneg_right hleft hX.le
      simpa [finiteA3RowFactor,mul_comm] using hh
    · have hh := mul_le_mul_of_nonneg_right hleft hX.le
      have hh' := mul_le_mul_of_nonneg_left hXY hV
      simpa [finiteA3RowFactor,mul_comm] using hh.trans hh'
  have hfrac : ‖x‖*‖x-y‖^6/‖finiteA3RowFactor x y i‖ ≤ V :=
    (div_le_iff₀ hrowpos).mpr hrow
  have hcoef : (707/40960 : ℝ)*V/‖y‖^6 ≤ R :=
    (div_le_iff₀ (by positivity)).mpr hR
  have hcoef' : (707/40960 : ℝ)*(‖x‖*‖x-y‖^6/‖finiteA3RowFactor x y i‖)/‖y‖^6 ≤ R := by
    apply le_trans _ hcoef
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfrac (by norm_num)) (by positivity)
  apply (finiteA3_residual_norm_lt_point x y c hx hy hc hxy hXY hXC i).trans_le
  calc
    _ = ((707/40960 : ℝ)*(‖x‖*‖x-y‖^6/‖finiteA3RowFactor x y i‖)/‖y‖^6)*
        (‖y‖^3/(‖x‖^4*‖c‖^5)) := by
      field_simp [hX.ne',hY.ne',hC.ne',hrowpos.ne']
      <;> ring
    _ ≤ R*(‖y‖^3/(‖x‖^4*‖c‖^5)) :=
      mul_le_mul_of_nonneg_right hcoef' (by positivity)
    _ = _ := by ring








end D1Bound5
end
