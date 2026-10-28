-- Prove2me | solution 1 for D1Bound5.finiteA5RowForm_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:26.888039+00:00
-- url     : https://prove2.me/submissions/bfdcaba9-aa09-42c3-9908-c98abd4dd5f8

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
import Definitions.Def_D1Bound5_FiniteA5IntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA5Residual_Definitions
import Theorems.Thm_D1Bound5_finiteA5Residual_explicit
import Theorems.Thm_D1Bound5_finiteA5RowForm_explicit
import Theorems.Thm_D1Bound5_finiteA5_height_scaled
import Theorems.Thm_D1Bound5_finiteA5_residual_norm_lt

section
open scoped NumberField
open Module

namespace D1Bound5





theorem _root_.solution (x y c z sX sY : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖)
    (herrorX : ‖(1+1/(x*c))^(1/2 : ℂ)-sX/(x*z)‖ <
      (101/100 : ℝ)*‖c‖/(‖x‖*‖z‖^2))
    (herrorY : ‖(1+1/(y*c))^(1/2 : ℂ)-sY/(y*z)‖ <
      (101/100 : ℝ)*‖c‖/(‖y‖*‖z‖^2)) (i : Fin 3) :
    ‖finiteA5RowForm x y c z sX sY i‖ <
      3113013*‖y‖^12*‖c‖^6/‖z‖ + (495/64 : ℝ)*‖y‖^5*‖z‖/(‖x‖^6*‖c‖^9) := by
  let L := finiteA5Left x y c i
  let R := finiteA5Right x y c i
  let θX : ℂ := (1+1/(x*c))^(1/2 : ℂ)
  let θY : ℂ := (1+1/(y*c))^(1/2 : ℂ)
  have hX := norm_pos_iff.mpr hx
  have hY := norm_pos_iff.mpr hy
  have hC := norm_pos_iff.mpr hc
  have hZ := norm_pos_iff.mpr hz
  have hid : finiteA5RowForm x y c z sX sY i =
      z*finiteA5Residual x y c i +
        z*((x*L)*(sX/(x*z)-θX)+(y*R)*(sY/(y*z)-θY)) := by
    rw [finiteA5RowForm_explicit,finiteA5Residual_explicit x y c hx hy hc]
    dsimp [L,R,θX,θY]
    field_simp [hx,hy,hz]
    <;> ring
  have hnorm : ‖finiteA5RowForm x y c z sX sY i‖ ≤
      ‖z‖*‖finiteA5Residual x y c i‖+
        ‖z‖*(‖x*L‖*‖θX-sX/(x*z)‖+‖y*R‖*‖θY-sY/(y*z)‖) := by
    rw [hid]
    calc
      _ ≤ ‖z*finiteA5Residual x y c i‖+
          ‖z*((x*L)*(sX/(x*z)-θX)+(y*R)*(sY/(y*z)-θY))‖ := norm_add_le _ _
      _ = ‖z‖*‖finiteA5Residual x y c i‖+
          ‖z‖*‖(x*L)*(sX/(x*z)-θX)+(y*R)*(sY/(y*z)-θY)‖ := by
        rw [norm_mul,norm_mul]
      _ ≤ ‖z‖*‖finiteA5Residual x y c i‖+
          ‖z‖*(‖(x*L)*(sX/(x*z)-θX)‖+‖(y*R)*(sY/(y*z)-θY)‖) := by
        gcongr
        exact norm_add_le _ _
      _ = _ := by
        simp only [norm_mul, norm_sub_rev (sX/(x*z)) θX,
          norm_sub_rev (sY/(y*z)) θY]
  have herrors :
      ‖z‖*(‖x*L‖*‖θX-sX/(x*z)‖+‖y*R‖*‖θY-sY/(y*z)‖) ≤
        (‖c‖/‖z‖)*((101/100 : ℝ)*(‖L‖+‖R‖)) := by
    calc
      _ ≤ ‖z‖*(‖x*L‖*((101/100 : ℝ)*‖c‖/(‖x‖*‖z‖^2))+
          ‖y*R‖*((101/100 : ℝ)*‖c‖/(‖y‖*‖z‖^2))) := by
        gcongr
      _ = _ := by
        rw [norm_mul,norm_mul]
        field_simp [hX.ne',hY.ne',hZ.ne']
        <;> ring
  have hYC : 1000 ≤ ‖y‖*‖c‖ :=
    hXC.trans (mul_le_mul_of_nonneg_right hXY hC.le)
  have hheight := finiteA5_height_scaled x y c hy hXY hYC i
  have herr :
      ‖z‖*(‖x*L‖*‖θX-sX/(x*z)‖+‖y*R‖*‖θY-sY/(y*z)‖) <
        3113013*‖y‖^12*‖c‖^6/‖z‖ := by
    apply herrors.trans_lt
    calc
      (‖c‖/‖z‖)*((101/100 : ℝ)*(‖L‖+‖R‖)) <
          (‖c‖/‖z‖)*(3113013*‖y‖^12*‖c‖^5) :=
        mul_lt_mul_of_pos_left hheight (div_pos hC hZ)
      _ = 3113013*‖y‖^12*‖c‖^6/‖z‖ := by ring
  have hres := mul_lt_mul_of_pos_left
    (finiteA5_residual_norm_lt x y c hx hy hc hxy hXY hXC i) hZ
  have hres' : ‖z‖*‖finiteA5Residual x y c i‖ <
      (495/64 : ℝ)*‖y‖^5*‖z‖/(‖x‖^6*‖c‖^9) := by
    calc
      ‖z‖*‖finiteA5Residual x y c i‖ <
          ‖z‖*((495/64 : ℝ)*‖y‖^5/(‖x‖^6*‖c‖^9)) := hres
      _ = (495/64 : ℝ)*‖y‖^5*‖z‖/(‖x‖^6*‖c‖^9) := by ring
  exact hnorm.trans_lt (by linarith only [herr,hres'])



end D1Bound5
end
