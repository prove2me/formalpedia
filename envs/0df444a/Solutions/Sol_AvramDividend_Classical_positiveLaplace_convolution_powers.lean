-- Prove2me | solution 1 for AvramDividend.Classical.positiveLaplace_convolution_powers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T20:47:22.17091+00:00
-- url     : https://prove2.me/submissions/37b5ffed-13e3-473c-8a23-8675bae057df

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positive_laplace_functional_convolution

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (κ : Measure ℝ) (m : ℕ → Measure ℝ) (θ : ℝ) (a : ℝ≥0∞)
    (hm0 : m 0 = Measure.dirac 0)
    (hmsucc : ∀ n : ℕ, m (n + 1) = Measure.conv κ (m n))
    (hsf : ∀ n : ℕ, SFinite (m n))
    (hκ : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂κ) = a) :
    ∀ n : ℕ,
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂m n) = a ^ n := by
  intro n
  induction n with
  | zero =>
      simp [hm0]
  | succ n ih =>
      letI : SFinite (m n) := hsf n
      rw [hmsucc n]
      rw [positive_laplace_functional_convolution κ (m n) θ]
      rw [hκ, ih]
      simp [pow_succ, mul_comm]
