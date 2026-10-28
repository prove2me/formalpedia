-- Prove2me | solution 1 for D1Bound5.finiteA5_residual_norm_lt_max_distance
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:19.046494+00:00
-- url     : https://prove2.me/submissions/4272dbe9-3cc2-439c-81bf-2c96762ab0c1

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
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA5Residual_Definitions
import Theorems.Thm_D1Bound5_finiteA5RowFactor_ne_zero
import Theorems.Thm_D1Bound5_finiteA5_residual_norm_lt_point

section
open scoped NumberField
open Module

namespace D1Bound5

/-- Actual A5 residual without any separation assumption between A
and |a-b|. The maximum preserves all three distinct row factors. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (R : ℝ)
    (hR : (9999/2621440 : ℝ)*max (‖x-y‖^10) (‖x‖*‖x-y‖^9) ≤ R*‖y‖^10)
    (i : Fin 3) :
    ‖finiteA5Residual x y c i‖ < R*‖y‖^5/(‖x‖^6*‖c‖^9) := by
  have hX := norm_pos_iff.mpr hx
  have hY := norm_pos_iff.mpr hy
  have hC := norm_pos_iff.mpr hc
  have hD := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hrowpos := norm_pos_iff.mpr (finiteA5RowFactor_ne_zero x y hx hy hxy i)
  let V := max (‖x-y‖^10) (‖x‖*‖x-y‖^9)
  have hleft : ‖x-y‖^10 ≤ V := le_max_left _ _
  have hright : ‖x‖*‖x-y‖^9 ≤ V := le_max_right _ _
  have hV : 0 ≤ V := (pow_nonneg hD.le 10).trans hleft
  have hrow : ‖x‖*‖x-y‖^10 ≤ V*‖finiteA5RowFactor x y i‖ := by
    fin_cases i
    · have hh := mul_le_mul_of_nonneg_right hright hD.le
      simpa only [finiteA5RowFactor,Matrix.cons_val_zero,Matrix.cons_val_zero'] using
        (show ‖x‖*‖x-y‖^10 ≤ V*‖x-y‖ by nlinarith only [hh])
    · have hh := mul_le_mul_of_nonneg_right hleft hX.le
      simpa [finiteA5RowFactor,mul_comm] using hh
    · have hh := mul_le_mul_of_nonneg_right hleft hX.le
      have hh' := mul_le_mul_of_nonneg_left hXY hV
      simpa [finiteA5RowFactor,mul_comm] using hh.trans hh'
  have hfrac : ‖x‖*‖x-y‖^10/‖finiteA5RowFactor x y i‖ ≤ V :=
    (div_le_iff₀ hrowpos).mpr hrow
  have hcoef : (9999/2621440 : ℝ)*V/‖y‖^10 ≤ R :=
    (div_le_iff₀ (by positivity)).mpr hR
  have hcoef' : (9999/2621440 : ℝ)*(‖x‖*‖x-y‖^10/‖finiteA5RowFactor x y i‖)/‖y‖^10 ≤ R := by
    apply le_trans _ hcoef
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfrac (by norm_num)) (by positivity)
  apply (finiteA5_residual_norm_lt_point x y c hx hy hc hxy hXY hXC i).trans_le
  calc
    _ = ((9999/2621440 : ℝ)*(‖x‖*‖x-y‖^10/‖finiteA5RowFactor x y i‖)/‖y‖^10)*
        (‖y‖^5/(‖x‖^6*‖c‖^9)) := by
      field_simp [hX.ne',hY.ne',hC.ne',hrowpos.ne']
      <;> ring
    _ ≤ R*(‖y‖^5/(‖x‖^6*‖c‖^9)) :=
      mul_le_mul_of_nonneg_right hcoef' (by positivity)
    _ = _ := by ring








end D1Bound5
end
