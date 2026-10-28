-- Prove2me | solution 1 for AvramDividend.Classical.causal_full_convolution_powers_zero_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:20:30.024209+00:00
-- url     : https://prove2.me/submissions/5d08e0f9-694e-4217-a3e4-d55331e0455e

import Theorems.Thm_AvramDividend_Classical_causal_convolution_zero_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory

/-- Iterated causal convolution has no mass at nonpositive times. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hFzero : F 0 = κ)
    (hFrec : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) :
    ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0 := by
  intro n
  induction n with
  | zero =>
      intro x hx
      rw [hFzero]
      exact hκzero x hx
  | succ n ih =>
      intro x hx
      rw [hFrec n]
      exact causal_convolution_zero_nonpositive κ (F n) hκzero ih x hx
