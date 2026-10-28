-- Prove2me | solution 1 for D1Bound5.coherent_three_remainder_envelope
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:57:35.431226+00:00
-- url     : https://prove2.me/submissions/ebfe894a-5a23-4ef4-a186-0a5d054b02ba

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
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_recurrence
import Theorems.Thm_D1Bound5_halfBinomialWeightedCoeff_norm_le

section
open Finset

namespace D1Bound5



private theorem coherent_three_coefficients :
    halfBinomialCoeff 3 = 1 / 16 ∧ halfBinomialCoeff 4 = -5 / 128 := by
  have h1 : halfBinomialCoeff 1 = 1 / 2 := by
    norm_num [halfBinomialCoeff, Ring.choose_one_right]
  have h2 : halfBinomialCoeff 2 = -1 / 8 := by
    have h := halfBinomialCoeff_recurrence 1
    norm_num [h1] at h
    linarith
  have h3 : halfBinomialCoeff 3 = 1 / 16 := by
    have h := halfBinomialCoeff_recurrence 2
    norm_num [h2] at h
    linarith
  refine ⟨h3, ?_⟩
  have h := halfBinomialCoeff_recurrence 3
  norm_num [h3] at h
  linarith

/-- A convenient envelope for the exact three-anchor tail bound.
It uses the sharp first coefficient of the tail; the resulting `1/3`
constant is sufficient for the manuscript's general estimate. -/
theorem _root_.solution
    (x y : ℂ) (A P : ℝ) (hA : 0 < A) (hP : 0 < P)
    (hx : ‖x‖ ≤ 1 / P) (hy : ‖y‖ ≤ 1 / P) (hAP : 9 ≤ A * P) :
    ‖halfBinomialWeightedCoeff x y 3‖ +
      (4 * |halfBinomialCoeff 4|) / P ^ 3 *
        (1 / (1 - 1 / (A * P)) ^ 3 - 1) ≤ 1 / (3 * P ^ 3) := by
  obtain ⟨hb3, hb4⟩ := coherent_three_coefficients
  have hc := halfBinomialWeightedCoeff_norm_le x y (1/P) (by positivity) hx hy 3 (by decide)
  rw [hb3] at hc
  norm_num only at hc
  have hc' : ‖halfBinomialWeightedCoeff x y 3‖ ≤ 1 / (4 * P ^ 3) := by
    calc
      _ ≤ (1 / 4 : ℝ) * (1 / P) ^ 3 := hc
      _ = _ := by field_simp <;> ring
  have hinv : 1 / (A * P) ≤ (1 / 9 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hAP
  have hbase : (8 / 9 : ℝ) ≤ 1 - 1 / (A * P) := by linarith
  have hbase3 : (512 / 729 : ℝ) ≤ (1 - 1 / (A * P)) ^ 3 := by
    have h : (8 / 9 : ℝ) ^ 3 ≤ (1 - 1 / (A * P)) ^ 3 := by gcongr
    norm_num only at h
    exact h
  have hfactor : 1 / (1 - 1 / (A * P)) ^ 3 - 1 ≤ (217 / 512 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 512 / 729) hbase3
    norm_num only at h
    linarith
  have ht : (4 * |halfBinomialCoeff 4|) / P ^ 3 *
      (1 / (1 - 1 / (A * P)) ^ 3 - 1) ≤ 1085 / (16384 * P ^ 3) := by
    rw [hb4]
    norm_num only
    calc
      (5 / 32 : ℝ) / P ^ 3 * (1 / (1 - 1 / (A * P)) ^ 3 - 1) ≤
          (5 / 32 : ℝ) / P ^ 3 * (217 / 512) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = _ := by field_simp [ne_of_gt hP] <;> ring
  calc
    _ ≤ 1 / (4 * P ^ 3) + 1085 / (16384 * P ^ 3) := add_le_add hc' ht
    _ ≤ 1 / (3 * P ^ 3) := by
      apply le_of_lt
      calc
        _ = ((1 / 4 : ℝ) + 1085 / 16384) / P ^ 3 := by field_simp <;> ring
        _ < (1 / 3 : ℝ) / P ^ 3 := div_lt_div_of_pos_right (by norm_num) (by positivity)
        _ = _ := by field_simp <;> ring





end D1Bound5
end
