-- Prove2me | solution 1 for D1Bound5.coherentRemainder_two_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:27.679263+00:00
-- url     : https://prove2.me/submissions/f08e29a4-338b-4dcf-9da4-cc5fdebc2add

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentFormBounds_Definitions
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_coherentRemainder_norm_sub_le
import Theorems.Thm_D1Bound5_halfBinomialCoeff_recurrence
import Theorems.Thm_D1Bound5_halfBinomialWeightedCoeff_two_norm_le

section
open Finset

namespace D1Bound5

private theorem coherent_halfCoeff_three : halfBinomialCoeff 3 = 1 / 16 := by
  have h1 : halfBinomialCoeff 1 = 1 / 2 := by
    norm_num [halfBinomialCoeff, Ring.choose_one_right]
  have h2 : halfBinomialCoeff 2 = -1 / 8 := by
    have h := halfBinomialCoeff_recurrence 1
    norm_num [h1] at h
    linarith
  have h := halfBinomialCoeff_recurrence 2
  norm_num [h2] at h
  linarith



/-- Under `AP >= 32` and the quarter-size reciprocal terminal bound,
the actual complete homogeneous remainder satisfies a uniform rational
estimate with room to spare. -/
theorem _root_.solution
    (a : Fin 2 → ℂ) (p q : ℂ) (A P : ℝ)
    (hA : 0 < A) (hP : 0 < P) (ha : ∀ i, A ≤ ‖a i‖)
    (hp : ‖p⁻¹‖ ≤ 1 / P) (hq : ‖q⁻¹‖ ≤ 1 / (4 * P))
    (hAP : 32 ≤ A * P) :
    ‖coherentRemainder a p q‖ ≤ 7 / (32 * P ^ 2) := by
  have hAP0 : 0 < A * P := by positivity
  have hq' : ‖q⁻¹‖ ≤ 1 / P := by
    exact hq.trans (one_div_le_one_div_of_le hP (by nlinarith))
  have ht := coherentRemainder_norm_sub_le a (by decide) p q A P hA hP ha hp hq'
    (by linarith)
  norm_num [coherent_halfCoeff_three] at ht
  have ht' : ‖coherentRemainder a p q - halfBinomialWeightedCoeff p⁻¹ q⁻¹ 2‖ ≤
      (1/4 : ℝ)/P^2*(1/(1-1/(A*P))^2-1) := by
    simpa only [one_div, mul_inv_rev] using ht
  have hcoeff := halfBinomialWeightedCoeff_two_norm_le p⁻¹ q⁻¹ P hP hp hq
  have hinv : 1 / (A * P) ≤ (1 / 32 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hAP
  have hbase : (31 / 32 : ℝ) ≤ 1 - 1 / (A * P) := by linarith
  have hbase0 : 0 ≤ 1 - 1 / (A * P) := by linarith
  have hbase2 : (961 / 1024 : ℝ) ≤ (1 - 1 / (A * P)) ^ 2 := by
    nlinarith only [hbase, hbase0, sq_nonneg (1 - 1 / (A * P) - 31 / 32)]
  have hfactor : 1 / (1 - 1 / (A * P)) ^ 2 - 1 ≤ (63 / 961 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 961 / 1024) hbase2
    norm_num at h
    have h' : 1/(1-1/(A*P))^2 ≤ (1024/961 : ℝ) := by
      simpa only [one_div, mul_inv_rev] using h
    linarith only [h']
  have htail : ‖coherentRemainder a p q - halfBinomialWeightedCoeff p⁻¹ q⁻¹ 2‖ ≤
      63 / (3844 * P ^ 2) := by
    calc
      _ ≤ (1 / 4 : ℝ) / P ^ 2 * (1 / (1 - 1 / (A * P)) ^ 2 - 1) := ht'
      _ ≤ (1 / 4 : ℝ) / P ^ 2 * (63 / 961) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = 63 / (3844 * P ^ 2) := by ring
  have hF : ‖coherentRemainder a p q‖ ≤
      ‖halfBinomialWeightedCoeff p⁻¹ q⁻¹ 2‖ +
        ‖coherentRemainder a p q - halfBinomialWeightedCoeff p⁻¹ q⁻¹ 2‖ := by
    have h := norm_add_le (halfBinomialWeightedCoeff p⁻¹ q⁻¹ 2)
      (coherentRemainder a p q - halfBinomialWeightedCoeff p⁻¹ q⁻¹ 2)
    have heq : halfBinomialWeightedCoeff p⁻¹ q⁻¹ 2 +
        (coherentRemainder a p q - halfBinomialWeightedCoeff p⁻¹ q⁻¹ 2) =
        coherentRemainder a p q := by ring
    rw [heq] at h
    exact h
  calc
    ‖coherentRemainder a p q‖ ≤
      25 / (128 * P ^ 2) + 63 / (3844 * P ^ 2) :=
        hF.trans (add_le_add hcoeff htail)
    _ ≤ 7 / (32 * P ^ 2) := by
      apply le_of_lt
      calc
        _ = ((25 / 128 : ℝ) + 63 / 3844) / P ^ 2 := by field_simp <;> ring
        _ < (7 / 32 : ℝ) / P ^ 2 :=
          div_lt_div_of_pos_right (by norm_num) (by positivity)
        _ = _ := by field_simp <;> ring





end D1Bound5
end
