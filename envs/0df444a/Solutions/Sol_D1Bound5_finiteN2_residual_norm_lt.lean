-- Prove2me | solution 1 for D1Bound5.finiteN2_residual_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:56:38.480902+00:00
-- url     : https://prove2.me/submissions/87de35f7-65e7-4a05-ab62-5c121d4cc4ba

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN2Residual_Definitions
import Theorems.Thm_D1Bound5_finiteN2_residual_norm_lt_point

section
namespace D1Bound5













/-- The table's uniform residual constant5/4 follows with strict slack. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (i : Fin 3) :
    ‖finiteN2Residual x y c i‖ < (5/4 : ℝ)*‖y‖^2/(‖x‖^3*‖c‖^4) := by
  have hX : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hY : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hC : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hδ : ‖x-y‖ ≤ 2*‖y‖ := (norm_sub_le x y).trans (by linarith only [hXY])
  have hδ4 : ‖x-y‖^4 ≤ 16*‖y‖^4 := by
    calc
      _ ≤ (2*‖y‖)^4 := by gcongr
      _ = _ := by ring
  have hδ3 : ‖x-y‖^3 ≤ 8*‖y‖^3 := by
    calc
      _ ≤ (2*‖y‖)^3 := by gcongr
      _ = _ := by ring
  have hxδ : ‖x‖*‖x-y‖^3 ≤ 16*‖y‖^4 := by
    calc
      _ ≤ ‖y‖*(8*‖y‖^3) := mul_le_mul hXY hδ3 (by positivity) (norm_nonneg _)
      _ ≤ _ := by nlinarith only [pow_nonneg (norm_nonneg y) 4]
  have hm := max_le hδ4 hxδ
  have h := finiteN2_residual_norm_lt_point x y c hx hy hc hxy hXY hXC i
  calc
    _ < _ := h
    _ ≤ (101/2560 : ℝ)*(16*‖y‖^4)/(‖x‖^3*‖y‖^2*‖c‖^4) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) (by positivity)
    _ = (101/160 : ℝ)*‖y‖^2/(‖x‖^3*‖c‖^4) := by
      field_simp [hX.ne',hY.ne',hC.ne']
      <;> ring
    _ < _ := by
      apply div_lt_div_of_pos_right _ (by positivity)
      exact mul_lt_mul_of_pos_right (by norm_num : (101/160 : ℝ) < 5/4) (by positivity)

end D1Bound5
end
