-- Prove2me | solution 1 for D1Bound5.finiteUnequalClearedEntry_residual_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:37:07.39682+00:00
-- url     : https://prove2.me/submissions/cb90a722-020a-4679-afc8-dd3f9df72e34

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
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteUnequalEntry_Definitions
import Definitions.Def_D1Bound5_UnequalPoleResidual_Definitions
import Theorems.Thm_D1Bound5_bennettTwoNodes_injective
import Theorems.Thm_D1Bound5_bennettTwoNodes_one
import Theorems.Thm_D1Bound5_bennettTwoNodes_two
import Theorems.Thm_D1Bound5_bennettTwoNodes_zero
import Theorems.Thm_D1Bound5_finiteUnequalClearedEntry_eq_scaled_residue
import Theorems.Thm_D1Bound5_finiteUnequalOrders_add_one
import Theorems.Thm_D1Bound5_finiteUnequalOrders_le
import Theorems.Thm_D1Bound5_unequalPolePolynomial_residual_norm_le

section
open Finset

namespace D1Bound5







theorem finiteUnequalOrders_total (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (i : Fin 3) :
    (∑ j, (finiteUnequalOrders k m i j+1)) = m+2*k+1 := by
  simp_rw [finiteUnequalOrders_add_one k m hk hm]
  fin_cases i <;> simp [Fin.sum_univ_three] <;> omega

variable {F : Type*} [Field F] [CharZero F]











theorem finiteUnequal_residual_scale (X Y C delta : ℝ)
    (hX : X ≠ 0) (hY : Y ≠ 0) (hC : C ≠ 0) (k m : ℕ) :
    (4^k*X^m*Y^m*delta^(2*k)*(X*Y*C)^k)*((X*Y*C)⁻¹)^(m+2*k) =
      4^k*delta^(2*k)/(X^k*Y^k*C^(m+k)) := by
  have hidx : m+2*k = m+k+k := by omega
  rw [hidx]
  simp only [pow_add,mul_pow,inv_pow]
  field_simp [hX,hY,hC]
  <;> ring

/-- Actual unequal-pole residual bound after clearing. The binomial factor
and tail degree remain exact, allowing the finite A3/A4/A5 constants to be
evaluated independently with rational arithmetic. -/
theorem _root_.solution
    (x y c : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1 < ‖x‖*‖c‖)
    (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k)
    (hs : (k : ℝ)+1/2 < (m+2*k : ℕ)) (i : Fin 3) :
    ‖∑ j, finiteUnequalClearedEntry x y c k m i j*
        (1+bennettTwoNodes x y j*(x*y*c)⁻¹)^(1/2 : ℂ)‖ ≤
      (4^k*‖x-y‖^(2*k)/(‖x‖^k*‖y‖^k*‖c‖^(m+k)))*
        |Ring.choose ((k : ℝ)+1/2) (m+2*k)| /
          (1-1/(‖x‖*‖c‖))^(((m+2*k : ℕ) : ℝ)-((k : ℝ)+1/2)) := by
  have hX : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hY : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hC : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hprod : 0 < ‖x‖*‖c‖ := lt_trans (by norm_num) hXC
  have hnorm : ‖(x*y*c)⁻¹‖ = (‖x‖*‖y‖*‖c‖)⁻¹ := by simp only [norm_inv,norm_mul]
  have hr : ‖y‖*‖(x*y*c)⁻¹‖ = 1/(‖x‖*‖c‖) := by
    rw [hnorm]
    field_simp [hX,hY,hC]
    <;> ring
  have hradius : ‖y‖*‖(x*y*c)⁻¹‖ < 1 := by
    rw [hr]
    exact (div_lt_one hprod).mpr hXC
  have hnodes : ∀ j, ‖bennettTwoNodes x y j‖ ≤ ‖y‖ := by
    intro j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    · simpa only [bennettTwoNodes_zero,norm_zero] using norm_nonneg y
    · simp only [bennettTwoNodes_one,le_refl]
    · simpa only [bennettTwoNodes_two] using hXY
  have htotal : (∑ j,(finiteUnequalOrders k m i j+1))-1 = m+2*k := by
    rw [finiteUnequalOrders_total k m hk hm i]
    omega
  have hbound := unequalPolePolynomial_residual_norm_le
    (bennettTwoNodes x y) (bennettTwoNodes_injective x y hx hy hxy)
    (finiteUnequalOrders k m i) 0 k (finiteUnequalOrders_le k m hmk i)
    (1/2) ‖y‖ ((x*y*c)⁻¹) (by simpa only [htotal] using hs)
    (norm_nonneg y) hnodes hradius
  rw [htotal] at hbound
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hbound
  let S : ℂ := 4^k*x^m*y^m*(x-y)^(2*k)*(x*y*c)^k
  have hrow : (∑ j, finiteUnequalClearedEntry x y c k m i j*
        (1+bennettTwoNodes x y j*(x*y*c)⁻¹)^(1/2 : ℂ)) =
      S*∑ j, (unequalPolePolynomial (bennettTwoNodes x y) (finiteUnequalOrders k m i)
        k (1/2 : ℂ) j).eval (x*y*c)⁻¹ *
          (1+bennettTwoNodes x y j*(x*y*c)⁻¹)^(1/2 : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [finiteUnequalClearedEntry_eq_scaled_residue x y c hx hy hc k m hmk i j]
    exact mul_assoc _ _ _
  have hscale : ‖S‖*‖(x*y*c)⁻¹‖^(m+2*k) =
      4^k*‖x-y‖^(2*k)/(‖x‖^k*‖y‖^k*‖c‖^(m+k)) := by
    rw [hnorm]
    have hSnorm : ‖S‖ = 4^k*‖x‖^m*‖y‖^m*‖x-y‖^(2*k)*(‖x‖*‖y‖*‖c‖)^k := by
      simp [S,norm_mul,norm_pow]
    rw [hSnorm]
    exact finiteUnequal_residual_scale ‖x‖ ‖y‖ ‖c‖ ‖x-y‖ hX hY hC k m
  rw [hrow,norm_mul]
  calc
    _ ≤ ‖S‖*(|Ring.choose ((k : ℝ)+1/2) (m+2*k)| *
        ‖(x*y*c)⁻¹‖^(m+2*k) /
          (1-‖y‖*‖(x*y*c)⁻¹‖)^(((m+2*k : ℕ) : ℝ)-((k : ℝ)+1/2))) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg S)
    _ = (‖S‖*‖(x*y*c)⁻¹‖^(m+2*k))*|Ring.choose ((k : ℝ)+1/2) (m+2*k)| /
        (1-1/(‖x‖*‖c‖))^(((m+2*k : ℕ) : ℝ)-((k : ℝ)+1/2)) := by
      rw [hr]
      ring
    _ = _ := by rw [hscale]

end D1Bound5
end
