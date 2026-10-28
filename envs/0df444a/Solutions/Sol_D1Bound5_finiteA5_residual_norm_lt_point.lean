-- Prove2me | solution 1 for D1Bound5.finiteA5_residual_norm_lt_point
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:32:18.569987+00:00
-- url     : https://prove2.me/submissions/c3720612-a5d9-4712-ac87-b3eacb9fa9f9

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
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA5Residual_Definitions
import Definitions.Def_D1Bound5_FiniteUnequalEntry_Definitions
import Theorems.Thm_D1Bound5_bennett_factorial_mul_abs_choose
import Theorems.Thm_D1Bound5_finiteA5RowFactor_ne_zero
import Theorems.Thm_D1Bound5_finiteA5_residual_sum_identity
import Theorems.Thm_D1Bound5_finiteUnequalClearedEntry_residual_norm_le
import Theorems.Thm_D1Bound5_finite_eta_reciprocal_lt

section
namespace D1Bound5



theorem finiteA5_beta : |Ring.choose (11/2 : ℝ) 14| = 495/33554432 := by
  have h := bennett_factorial_mul_abs_choose (11/2 : ℝ) 14
  norm_num [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ] at h
  nlinarith only [h]





/-- Exact pointwise residual with the actual row factor retained, suitable
for the fixed-anchor refinement as well as the uniform family bound. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (i : Fin 3) :
    ‖finiteA5Residual x y c i‖ <
      (101/100 : ℝ)*(495/33554432)*(4^5*‖x-y‖^10/(‖x‖^5*‖y‖^5*‖c‖^9)) /
        (4*‖finiteA5RowFactor x y i‖) := by
  have hbase : 0 < 4^5*‖x-y‖^10/(‖x‖^5*‖y‖^5*‖c‖^9) := by
    have hX := norm_pos_iff.mpr hx
    have hY := norm_pos_iff.mpr hy
    have hC := norm_pos_iff.mpr hc
    have hD := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    positivity
  have hrow : 0 < ‖finiteA5RowFactor x y i‖ :=
    norm_pos_iff.mpr (finiteA5RowFactor_ne_zero x y hx hy hxy i)
  have hres := finiteUnequalClearedEntry_residual_norm_le x y c hx hy hc hxy
    hXY (by linarith) 5 4 (by decide) (by decide) (by decide) (by norm_num) i
  norm_num only [Nat.cast_ofNat] at hres
  rw [finiteA5_beta] at hres
  have heta := finite_eta_reciprocal_lt (‖x‖*‖c‖) (17/2 : ℝ) hXC (by norm_num)
  have hbound :
      ‖∑ j, finiteUnequalClearedEntry x y c 5 4 i j*
          (1+bennettTwoNodes x y j*(x*y*c)⁻¹)^(1/2 : ℂ)‖ <
        (101/100 : ℝ)*(495/33554432)*(4^5*‖x-y‖^10/(‖x‖^5*‖y‖^5*‖c‖^9)) := by
    apply hres.trans_lt
    have hm := mul_lt_mul_of_pos_left heta (mul_pos hbase (by norm_num : (0 : ℝ) < 495/33554432))
    convert hm using 1 <;> ring
  rw [← finiteA5_residual_sum_identity x y c hx hy hxy i,norm_mul,norm_mul] at hbound
  norm_num only [Complex.norm_ofNat] at hbound
  exact (lt_div_iff₀ (by positivity)).mpr (by nlinarith only [hbound])





end D1Bound5
end
