-- Prove2me | solution 1 for D1Bound5.unit_pair_symmetric_complex_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:51.879234+00:00
-- url     : https://prove2.me/submissions/6092191b-549e-41f1-9044-3aa64fc7baaf

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open scoped NumberField
open Module

namespace D1Bound5



/-- The numerical contradiction behind the symmetric-five obstruction.
The two lower bounds will be supplied by integrality of the factors. -/
theorem _root_.solution
    (a b G J : ℂ) (hA : 3 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖)
    (hG : G = 2 * a ^ 2 * b ^ 2 - a ^ 2 - 1)
    (hid : (G - J) * (G + J) = (a ^ 2 - 1) ^ 2)
    (hm : 1 ≤ ‖G - J‖) (hp : 1 ≤ ‖G + J‖) : False := by
  have hsum : ‖G - J‖ + ‖G + J‖ ≤ ‖G - J‖ * ‖G + J‖ + 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hp)]
  have htriangle : 2 * ‖G‖ ≤ ‖G - J‖ + ‖G + J‖ := by
    have h := norm_add_le (G - J) (G + J)
    have he : (G - J) + (G + J) = 2 * G := by ring
    rw [he, norm_mul, Complex.norm_two] at h
    exact h
  have hprod : ‖G - J‖ * ‖G + J‖ = ‖a ^ 2 - 1‖ ^ 2 := by
    simpa only [norm_mul, norm_pow] using congrArg norm hid
  have hsub : ‖a ^ 2 - 1‖ ≤ ‖a‖ ^ 2 + 1 := by
    calc
      ‖a ^ 2 - 1‖ ≤ ‖a ^ 2‖ + ‖(1 : ℂ)‖ := norm_sub_le (a ^ 2) (1 : ℂ)
      _ = _ := by rw [Complex.norm_pow, norm_one]
  have hsubsq : ‖a ^ 2 - 1‖ ^ 2 ≤ (‖a‖ ^ 2 + 1) ^ 2 := by
    nlinarith only [hsub, norm_nonneg (a ^ 2 - 1), sq_nonneg ‖a‖]
  have hupper : 2 * ‖G‖ ≤ (‖a‖ ^ 2 + 1) ^ 2 + 1 := by
    nlinarith only [htriangle, hsum, hprod, hsubsq]
  have hlower : 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2 ≤ ‖G‖ + ‖a‖ ^ 2 + 1 := by
    have h1 := norm_add_le G (a ^ 2)
    have h2 := norm_add_le (G + a ^ 2) (1 : ℂ)
    have he : G + a ^ 2 + 1 = 2 * a ^ 2 * b ^ 2 := by rw [hG]; ring
    rw [he] at h2
    simp only [norm_mul, norm_pow, norm_one, Complex.norm_two] at h1 h2
    linarith
  have hAsq : 9 ≤ ‖a‖ ^ 2 := by nlinarith only [hA, sq_nonneg (‖a‖ - 3)]
  have hABsq : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    nlinarith only [hAB, norm_nonneg a, norm_nonneg b]
  have hprodlo : ‖a‖ ^ 4 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hABsq (sq_nonneg ‖a‖)
    nlinarith only [h]
  nlinarith only [hlower, hupper, hprodlo, hAsq, sq_nonneg (‖a‖ ^ 2 - 9)]







end D1Bound5
end
