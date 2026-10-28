-- Prove2me | solution 1 for AvramDividend.Classical.causal_exponential_convolution_power_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:32:06.937434+00:00
-- url     : https://prove2.me/submissions/25061fe3-eb0e-4a04-938e-f977d9064cd1

import Theorems.Thm_AvramDividend_Classical_exponential_causal_convolution_factorisation
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Exponential damping transports every convolution power recurrence. -/
theorem solution
    (f : ℝ → ℝ) (U : ℕ → ℝ → ℝ) (θ : ℝ)
    (hU0 : U 0 = f)
    (hUrec : ∀ n : ℕ, ∀ x : ℝ,
      U (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, f (x - s) * U n s ∂volume) :
    (fun x : ℝ => Real.exp (-(θ * x)) * U 0 x) =
      (fun x : ℝ => Real.exp (-(θ * x)) * f x) ∧
    (∀ n : ℕ, ∀ x : ℝ,
      Real.exp (-(θ * x)) * U (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x,
          (Real.exp (-(θ * (x - s))) * f (x - s)) *
          (Real.exp (-(θ * s)) * U n s) ∂volume) := by
  constructor
  · funext x
    rw [hU0]
  · intro n x
    rw [hUrec n x]
    exact exponential_causal_convolution_factorisation f (U n) θ x
