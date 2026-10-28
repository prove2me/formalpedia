-- Prove2me | solution 1 for D1Bound5.regular_quadruple_norm_lt_five
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:11.69532+00:00
-- url     : https://prove2.me/submissions/58c3fb74-85a7-42d0-acbd-9408e86dd2f4

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
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherent_two_scalar_size_bound
import Theorems.Thm_D1Bound5_regular_quadruple_eq_extensions

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5





/-- A regular complex quadruple with the size hypotheses used in the
strong two-anchor lemma has `Q < 5 A B P`. -/
theorem _root_.solution
    (a b p q r s t : ℂ)
    (hr : r ^ 2 = a * b + 1) (hs : s ^ 2 = a * p + 1)
    (ht : t ^ 2 = b * p + 1)
    (hreg : (a + b - p - q) ^ 2 = 4 * (a * b + 1) * (p * q + 1))
    (hA : 1 ≤ ‖a‖) (hB : 3 ≤ ‖b‖) (hP : 5 * ‖b‖ ≤ ‖p‖) :
    ‖q‖ < 5 * ‖a‖ * ‖b‖ * ‖p‖ := by
  have hroot (u v w : ℂ) (hw : w ^ 2 = u * v + 1) :
      ‖w‖ ^ 2 ≤ ‖u‖ * ‖v‖ + 1 := by
    calc
      ‖w‖ ^ 2 = ‖w ^ 2‖ := (norm_pow w 2).symm
      _ = ‖u * v + 1‖ := by rw [hw]
      _ ≤ ‖u‖ * ‖v‖ + 1 := by
        simpa only [norm_mul, norm_one] using norm_add_le (u * v) (1 : ℂ)
  have hnr := hroot a b r hr
  have hns := hroot a p s hs
  have hnt := hroot b p t ht
  have hU : ‖r * s * t‖ ^ 2 ≤
      (‖a‖ * ‖b‖ + 1) * (‖a‖ * ‖p‖ + 1) * (‖b‖ * ‖p‖ + 1) := by
    rw [norm_mul, norm_mul, mul_pow, mul_pow]
    exact mul_le_mul (mul_le_mul hnr hns (sq_nonneg _) (by positivity)) hnt
      (sq_nonneg _) (by positivity)
  have hcenter : ‖a + b + p + 2 * a * b * p‖ ≤
      ‖a‖ + ‖b‖ + ‖p‖ + 2 * ‖a‖ * ‖b‖ * ‖p‖ := by
    have h1 := norm_add_le a b
    have h2 := norm_add_le (a + b) p
    have h3 := norm_add_le (a + b + p) (2 * a * b * p)
    simp only [norm_mul, Complex.norm_two] at h3
    linarith
  have hpert : ‖(2 : ℂ) * (r * s * t)‖ = 2 * ‖r * s * t‖ := by
    rw [norm_mul, Complex.norm_two]
  have hQ : ‖q‖ ≤ ‖a‖ + ‖b‖ + ‖p‖ + 2 * ‖a‖ * ‖b‖ * ‖p‖ +
      2 * ‖r * s * t‖ := by
    rcases regular_quadruple_eq_extensions a b p q r s t hr hs ht hreg with h | h
    · rw [h]
      have hh := norm_add_le (a + b + p + 2 * a * b * p) (2 * (r * s * t))
      rw [hpert] at hh
      linarith
    · rw [h]
      have hh := norm_sub_le (a + b + p + 2 * a * b * p) (2 * (r * s * t))
      rw [hpert] at hh
      linarith
  exact coherent_two_scalar_size_bound ‖a‖ ‖b‖ ‖p‖ ‖r * s * t‖ ‖q‖
    hA hB hP (norm_nonneg _) hU hQ





end D1Bound5
end
