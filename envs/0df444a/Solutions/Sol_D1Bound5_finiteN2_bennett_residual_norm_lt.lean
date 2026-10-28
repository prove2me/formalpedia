-- Prove2me | solution 1 for D1Bound5.finiteN2_bennett_residual_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:33.62037+00:00
-- url     : https://prove2.me/submissions/89db0400-b23e-428e-aec4-39e1903b0273

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
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_residual_norm_le
import Theorems.Thm_D1Bound5_bennett_factorial_mul_abs_choose
import Theorems.Thm_D1Bound5_bennett_two_residual_choose_abs_Gamma
import Theorems.Thm_D1Bound5_finite_eta_reciprocal_lt

section
namespace D1Bound5





theorem finiteN2_choose_abs : |Ring.choose (5/2 : ℝ) 6| = 5/1024 := by
  have h := bennett_factorial_mul_abs_choose (5/2 : ℝ) 6
  rw [descPochhammer_eval_eq_prod_range] at h
  norm_num [Finset.prod_range_succ] at h
  nlinarith only [h]

theorem finiteN2_Gamma_beta :
    Real.Gamma (7/2)*Real.Gamma (7/2)/(Real.pi*Real.Gamma 7) = (5/1024 : ℝ) := by
  have h : |Ring.choose (5/2 : ℝ) 6| =
      Real.Gamma (7/2)*Real.Gamma (7/2)/(Real.pi*Real.Gamma 7) := by
    convert bennett_two_residual_choose_abs_Gamma 2 (by norm_num) using 1 <;> norm_num
  rw [finiteN2_choose_abs] at h
  exact h.symm

/-- A distance-sensitive bound for the actual unnormalized k=2 matrix,
deduced from the proved analytic residual and the rational eta estimate. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (i : Fin 3) :
    ‖∑ j, bennettTwoClearedEntry x y c 2 i j *
      (1+bennettTwoNodes x y j*(x*y*c)⁻¹)^(1/2 : ℂ)‖ <
      (101/1280 : ℝ)*‖x-y‖^4/(‖x‖^2*‖y‖^2*‖c‖^4) := by
  have hX : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hY : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hC : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hδ : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h := bennettTwoClearedEntry_residual_norm_le x y c hx hy hc hxy
    hXY (by linarith only [hXC]) 2 (by norm_num) i
  have hb : ‖∑ j, bennettTwoClearedEntry x y c 2 i j *
        (1+bennettTwoNodes x y j*(x*y*c)⁻¹)^(1/2 : ℂ)‖ ≤
      (4*‖x-y‖^2/(‖x‖*‖y‖*‖c‖^2))^2 *
        (Real.Gamma (7/2)*Real.Gamma (7/2)/(Real.pi*Real.Gamma 7)) /
          (1-1/(‖x‖*‖c‖))^(7/2 : ℝ) := by
    convert h using 1 <;> norm_num
  have hscale : (4*‖x-y‖^2/(‖x‖*‖y‖*‖c‖^2))^2*(5/1024 : ℝ) =
      (5/64 : ℝ)*‖x-y‖^4/(‖x‖^2*‖y‖^2*‖c‖^4) := by
    field_simp [hX.ne',hY.ne',hC.ne']
    <;> ring
  rw [finiteN2_Gamma_beta,hscale] at hb
  have heta := finite_eta_reciprocal_lt (‖x‖*‖c‖) (7/2) hXC (by norm_num)
  calc
    _ ≤ ((5/64 : ℝ)*‖x-y‖^4/(‖x‖^2*‖y‖^2*‖c‖^4))*
        (1/(1-1/(‖x‖*‖c‖))^(7/2 : ℝ)) := by simpa only [div_eq_mul_inv,one_mul] using hb
    _ < ((5/64 : ℝ)*‖x-y‖^4/(‖x‖^2*‖y‖^2*‖c‖^4))*(101/100) :=
      mul_lt_mul_of_pos_left heta (by positivity)
    _ = _ := by ring





end D1Bound5
end
