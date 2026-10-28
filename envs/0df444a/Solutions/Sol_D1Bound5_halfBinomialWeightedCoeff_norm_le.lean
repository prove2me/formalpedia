-- Prove2me | solution 1 for D1Bound5.halfBinomialWeightedCoeff_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:38.208258+00:00
-- url     : https://prove2.me/submissions/b358bcd7-8027-45f5-a8e9-b515f299db10

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_abs_convolution

section
open Finset

namespace D1Bound5



/-- The sharp real absolute convolution implies a uniform complex coefficient
bound, without assuming x=y or positivity of either complex variable. -/
theorem _root_.solution
    (x y : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hx : ‖x‖ ≤ t) (hy : ‖y‖ ≤ t)
    (n : ℕ) (hn : 2 ≤ n) :
    ‖halfBinomialWeightedCoeff x y n‖ ≤
      4 * |halfBinomialCoeff n| * t ^ n := by
  unfold halfBinomialWeightedCoeff
  have hterm (ij : ℕ × ℕ) (hij : ij ∈ Finset.antidiagonal n) :
      ‖((halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2 : ℝ) : ℂ) *
        x ^ ij.1 * y ^ ij.2‖ ≤
      |halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2| * t ^ n := by
    have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    calc
      ‖((halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2 : ℝ) : ℂ) *
          x ^ ij.1 * y ^ ij.2‖ =
        |halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2| *
          ‖x‖ ^ ij.1 * ‖y‖ ^ ij.2 := by
            simp [Real.norm_eq_abs]
      _ ≤ |halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2| *
          t ^ ij.1 * t ^ ij.2 := by
            gcongr
      _ = |halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2| * t ^ n := by
            rw [mul_assoc, ← pow_add, hsum]
  calc
    ‖∑ ij ∈ Finset.antidiagonal n,
        ((halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2 : ℝ) : ℂ) *
          x ^ ij.1 * y ^ ij.2‖ ≤
      ∑ ij ∈ Finset.antidiagonal n,
        ‖((halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2 : ℝ) : ℂ) *
          x ^ ij.1 * y ^ ij.2‖ := norm_sum_le _ _
    _ ≤ ∑ ij ∈ Finset.antidiagonal n,
        |halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2| * t ^ n := by
          exact Finset.sum_le_sum (fun ij hij => hterm ij hij)
    _ = (∑ ij ∈ Finset.antidiagonal n,
        |halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2|) * t ^ n := by
          rw [Finset.sum_mul]
    _ = 4 * |halfBinomialCoeff n| * t ^ n := by
          rw [halfBinomialCoeff_abs_convolution n hn]





end D1Bound5
end
