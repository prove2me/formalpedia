-- Prove2me | solution 1 for D1Bound5.finiteA4RowForm_norm_lt_refined
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:28:57.676312+00:00
-- url     : https://prove2.me/submissions/bba991b8-045c-4887-8042-14a38c2833e1

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
import Definitions.Def_D1Bound5_FiniteA4IntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA4Residual_Definitions
import Theorems.Thm_D1Bound5_finiteA4Residual_explicit
import Theorems.Thm_D1Bound5_finiteA4RowForm_explicit
import Theorems.Thm_D1Bound5_finiteA4_residual_norm_lt_refined

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
      (101/100 : ℝ)*‖c‖/(‖y‖*‖z‖^2)) (i : Fin 3) (M R : ℝ)
    (hheight : (101/100 : ℝ)*(‖finiteA4Left x y c i‖+‖finiteA4Right x y c i‖) <
      M*‖y‖^9*‖c‖^4)
    (hdelta : ‖x‖ ≤ ‖x-y‖)
    (hR : (6363/409600 : ℝ)*‖x-y‖^8 ≤ R*‖y‖^8) :
    ‖finiteA4RowForm x y c z sX sY i‖ <
      M*‖y‖^9*‖c‖^5/‖z‖ + R*‖y‖^4*‖z‖/(‖x‖^5*‖c‖^7) := by
  let L := finiteA4Left x y c i
  let Lright := finiteA4Right x y c i
  let θX : ℂ := (1+1/(x*c))^(1/2 : ℂ)
  let θY : ℂ := (1+1/(y*c))^(1/2 : ℂ)
  have hX := norm_pos_iff.mpr hx
  have hY := norm_pos_iff.mpr hy
  have hC := norm_pos_iff.mpr hc
  have hZ := norm_pos_iff.mpr hz
  have hid : finiteA4RowForm x y c z sX sY i =
      z*finiteA4Residual x y c i +
        z*((x*L)*(sX/(x*z)-θX)+(y*Lright)*(sY/(y*z)-θY)) := by
    rw [finiteA4RowForm_explicit,finiteA4Residual_explicit x y c hx hy hc]
    dsimp [L,Lright,θX,θY]
    field_simp [hx,hy,hz]
    <;> ring
  have hnorm : ‖finiteA4RowForm x y c z sX sY i‖ ≤
      ‖z‖*‖finiteA4Residual x y c i‖+
        ‖z‖*(‖x*L‖*‖θX-sX/(x*z)‖+‖y*Lright‖*‖θY-sY/(y*z)‖) := by
    rw [hid]
    calc
      _ ≤ ‖z*finiteA4Residual x y c i‖+
          ‖z*((x*L)*(sX/(x*z)-θX)+(y*Lright)*(sY/(y*z)-θY))‖ := norm_add_le _ _
      _ = ‖z‖*‖finiteA4Residual x y c i‖+
          ‖z‖*‖(x*L)*(sX/(x*z)-θX)+(y*Lright)*(sY/(y*z)-θY)‖ := by
        rw [norm_mul,norm_mul]
      _ ≤ ‖z‖*‖finiteA4Residual x y c i‖+
          ‖z‖*(‖(x*L)*(sX/(x*z)-θX)‖+‖(y*Lright)*(sY/(y*z)-θY)‖) := by
        gcongr
        exact norm_add_le _ _
      _ = _ := by
        simp only [norm_mul, norm_sub_rev (sX/(x*z)) θX,
          norm_sub_rev (sY/(y*z)) θY]
  have herrors :
      ‖z‖*(‖x*L‖*‖θX-sX/(x*z)‖+‖y*Lright‖*‖θY-sY/(y*z)‖) ≤
        (‖c‖/‖z‖)*((101/100 : ℝ)*(‖L‖+‖Lright‖)) := by
    calc
      _ ≤ ‖z‖*(‖x*L‖*((101/100 : ℝ)*‖c‖/(‖x‖*‖z‖^2))+
          ‖y*Lright‖*((101/100 : ℝ)*‖c‖/(‖y‖*‖z‖^2))) := by
        gcongr
      _ = _ := by
        rw [norm_mul,norm_mul]
        field_simp [hX.ne',hY.ne',hZ.ne']
        <;> ring
  have hYC : 1000 ≤ ‖y‖*‖c‖ :=
    hXC.trans (mul_le_mul_of_nonneg_right hXY hC.le)
  have herr :
      ‖z‖*(‖x*L‖*‖θX-sX/(x*z)‖+‖y*Lright‖*‖θY-sY/(y*z)‖) <
        M*‖y‖^9*‖c‖^5/‖z‖ := by
    apply herrors.trans_lt
    calc
      (‖c‖/‖z‖)*((101/100 : ℝ)*(‖L‖+‖Lright‖)) <
          (‖c‖/‖z‖)*(M*‖y‖^9*‖c‖^4) :=
        mul_lt_mul_of_pos_left hheight (div_pos hC hZ)
      _ = M*‖y‖^9*‖c‖^5/‖z‖ := by ring
  have hres := mul_lt_mul_of_pos_left
    (finiteA4_residual_norm_lt_refined x y c hx hy hc hxy hXY hXC hdelta R hR i) hZ
  have hres' : ‖z‖*‖finiteA4Residual x y c i‖ <
      R*‖y‖^4*‖z‖/(‖x‖^5*‖c‖^7) := by
    calc
      ‖z‖*‖finiteA4Residual x y c i‖ <
          ‖z‖*(R*‖y‖^4/(‖x‖^5*‖c‖^7)) := hres
      _ = R*‖y‖^4*‖z‖/(‖x‖^5*‖c‖^7) := by ring
  exact hnorm.trans_lt (by linarith only [herr,hres'])






end D1Bound5
end
