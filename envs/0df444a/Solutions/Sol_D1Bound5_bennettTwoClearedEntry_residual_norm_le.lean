-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_residual_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:45:45.423985+00:00
-- url     : https://prove2.me/submissions/caee2116-227b-4fb9-904e-2c42f513e6f8

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
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_eq_scaled_residue
import Theorems.Thm_D1Bound5_bennettTwoNodes_injective
import Theorems.Thm_D1Bound5_bennett_two_polynomial_residual_norm_le

section
open Finset

namespace D1Bound5

/-- Exact cancellation of the clearing factor with the order-three-k zero.
This is the source of the manuscript's residual scale 4 delta^2/(AB C^2). -/
theorem bennett_two_residual_scale (A B C δ : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (k : ℕ) :
    (4 * (A * B) ^ 2 * C * δ ^ 2) ^ k * ((A * B * C)⁻¹) ^ (3 * k) =
      (4 * δ ^ 2 / (A * B * C ^ 2)) ^ k := by
  rw [pow_mul, ← mul_pow]
  congr 1
  field_simp
  <;> ring

/-- The actual integral two-anchor Q-matrix satisfies the manuscript's
Gamma residual bound. All factors are constructed entries; no approximation
or contour bound is provided as a hypothesis. -/
theorem _root_.solution
    (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≠ b)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1 < ‖a‖ * ‖c‖)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ‖∑ j, bennettTwoClearedEntry a b c k i j *
        (1 + bennettTwoNodes a b j * (a * b * c)⁻¹) ^ (1 / 2 : ℂ)‖ ≤
      (4 * ‖a - b‖ ^ 2 / (‖a‖ * ‖b‖ * ‖c‖ ^ 2)) ^ k *
        (Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma (2 * (k : ℝ) - 1 / 2) /
          (Real.pi * Real.Gamma (3 * (k : ℝ) + 1))) /
            (1 - 1 / (‖a‖ * ‖c‖)) ^ (2 * (k : ℝ) - 1 / 2) := by
  have hA : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hB : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hC : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hprod : 0 < ‖a‖ * ‖c‖ := lt_trans (by norm_num) hAC
  have hx : ‖(a * b * c)⁻¹‖ = (‖a‖ * ‖b‖ * ‖c‖)⁻¹ := by
    simp only [norm_inv, norm_mul]
  have hr : ‖b‖ * ‖(a * b * c)⁻¹‖ = 1 / (‖a‖ * ‖c‖) := by
    rw [hx]
    field_simp
    <;> ring
  have hradius : ‖b‖ * ‖(a * b * c)⁻¹‖ < 1 := by
    rw [hr]
    exact (div_lt_one hprod).mpr hAC
  have hnodes : ∀ j, ‖bennettTwoNodes a b j‖ ≤ ‖b‖ := by
    intro j
    fin_cases j <;> simp [bennettTwoNodes, hAB]
  have hbound := bennett_two_polynomial_residual_norm_le
    (bennettTwoNodes a b) (bennettTwoNodes_injective a b ha hb hab)
    k hk ‖b‖ ((a * b * c)⁻¹) i (norm_nonneg b) hnodes hradius
  let S : ℂ := (4 * (a * b) ^ 2 * c * (a - b) ^ 2) ^ k
  have hrow : (∑ j, bennettTwoClearedEntry a b c k i j *
        (1 + bennettTwoNodes a b j * (a * b * c)⁻¹) ^ (1 / 2 : ℂ)) =
      S * ∑ j, (bennettPolynomialResidue univ (bennettTwoNodes a b) k
        (1 / 2 : ℂ) i j).eval ((a * b * c)⁻¹) *
          (1 + bennettTwoNodes a b j * (a * b * c)⁻¹) ^ (1 / 2 : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [bennettTwoClearedEntry_eq_scaled_residue a b c ha hb hc]
    exact mul_assoc _ _ _
  have hscale : ‖S‖ * ‖(a * b * c)⁻¹‖ ^ (3 * k) =
      (4 * ‖a - b‖ ^ 2 / (‖a‖ * ‖b‖ * ‖c‖ ^ 2)) ^ k := by
    rw [hx]
    have hSnorm : ‖S‖ = (4 * (‖a‖ * ‖b‖) ^ 2 * ‖c‖ * ‖a - b‖ ^ 2) ^ k := by
      simp [S, norm_mul, norm_pow]
    rw [hSnorm]
    exact bennett_two_residual_scale ‖a‖ ‖b‖ ‖c‖ ‖a - b‖ hA hB hC k
  rw [hrow, norm_mul]
  calc
    _ ≤ ‖S‖ *
        ((Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma (2 * (k : ℝ) - 1 / 2) /
          (Real.pi * Real.Gamma (3 * (k : ℝ) + 1))) *
            ‖(a * b * c)⁻¹‖ ^ (3 * k) /
              (1 - ‖b‖ * ‖(a * b * c)⁻¹‖) ^ (2 * (k : ℝ) - 1 / 2)) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg S)
    _ = (‖S‖ * ‖(a * b * c)⁻¹‖ ^ (3 * k)) *
        (Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma (2 * (k : ℝ) - 1 / 2) /
          (Real.pi * Real.Gamma (3 * (k : ℝ) + 1))) /
            (1 - 1 / (‖a‖ * ‖c‖)) ^ (2 * (k : ℝ) - 1 / 2) := by
      rw [hr]
      ring
    _ = _ := by rw [hscale]

end D1Bound5
end
