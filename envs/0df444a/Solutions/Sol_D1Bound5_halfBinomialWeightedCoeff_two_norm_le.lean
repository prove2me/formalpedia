-- Prove2me | solution 1 for D1Bound5.halfBinomialWeightedCoeff_two_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:29.02063+00:00
-- url     : https://prove2.me/submissions/63bef47e-d002-493d-a4e9-07d755d6ee38

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
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_halfBinomialCoeff_recurrence

section
open Finset

namespace D1Bound5

private theorem halfCoeff_zero : halfBinomialCoeff 0 = 1 := by
  norm_num [halfBinomialCoeff]

private theorem halfCoeff_one : halfBinomialCoeff 1 = 1 / 2 := by
  norm_num [halfBinomialCoeff, Ring.choose_one_right]

private theorem halfCoeff_two : halfBinomialCoeff 2 = -1 / 8 := by
  have h := halfBinomialCoeff_recurrence 1
  norm_num [halfCoeff_one] at h
  linarith





/-- Frozen v4 equation (integrated-5), degree two. -/
theorem halfBinomialWeightedCoeff_two (x y : ℂ) :
    halfBinomialWeightedCoeff x y 2 = -(x - y)^2 / 8 := by
  norm_num [halfBinomialWeightedCoeff, Finset.antidiagonal,
    halfCoeff_zero, halfCoeff_one, halfCoeff_two]
  ring





end D1Bound5
end

section
open Finset

namespace D1Bound5



/-- The sharper degree-two coefficient bound uses the manuscript's
terminal separation, rather than the generic convolution envelope. -/
theorem _root_.solution
    (x y : ℂ) (P : ℝ) (hP : 0 < P)
    (hx : ‖x‖ ≤ 1 / P) (hy : ‖y‖ ≤ 1 / (4 * P)) :
    ‖halfBinomialWeightedCoeff x y 2‖ ≤ 25 / (128 * P ^ 2) := by
  have hxy : ‖x - y‖ ≤ 5 / (4 * P) := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 1 / P + 1 / (4 * P) := add_le_add hx hy
      _ = 5 / (4 * P) := by field_simp; ring
  have hsquare : ‖x - y‖ ^ 2 ≤ (5 / (4 * P)) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hxy)
      (add_nonneg (norm_nonneg (x-y)) (by positivity : 0 ≤ 5 / (4 * P)))
    nlinarith only [h]
  calc
    ‖halfBinomialWeightedCoeff x y 2‖ = ‖x - y‖ ^ 2 / 8 := by
      rw [halfBinomialWeightedCoeff_two, norm_div, norm_neg, norm_pow]
      norm_num
    _ ≤ (5 / (4 * P)) ^ 2 / 8 := div_le_div_of_nonneg_right hsquare (by norm_num)
    _ = 25 / (128 * P ^ 2) := by field_simp; ring







end D1Bound5
end
