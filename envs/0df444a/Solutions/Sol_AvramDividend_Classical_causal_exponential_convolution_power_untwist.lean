-- Prove2me | solution 1 for AvramDividend.Classical.causal_exponential_convolution_power_untwist
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:36:25.969131+00:00
-- url     : https://prove2.me/submissions/ecdaecde-162f-43c0-a259-d9265cf53cdb

import Theorems.Thm_AvramDividend_Classical_exponential_causal_convolution_factorisation
open AvramDividend.Classical MeasureTheory Set
theorem solution
    (f K : ℝ → ℝ) (F U : ℕ → ℝ → ℝ) (θ : ℝ)
    (hK : ∀ x : ℝ, K x = Real.exp (-(θ * x)) * f x)
    (hF0 : F 0 = K)
    (hFrec : ∀ n : ℕ, ∀ x : ℝ, F (n + 1) x =
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * F n s ∂volume)
    (hU0 : U 0 = f)
    (hUrec : ∀ n : ℕ, ∀ x : ℝ, U (n + 1) x =
      ∫ s in Ioc (0 : ℝ) x, f (x - s) * U n s ∂volume) :
    ∀ n : ℕ, ∀ x : ℝ,
      F n x = Real.exp (-(θ * x)) * U n x := by 
  intro n
  induction n with
  | zero => intro x; rw [hF0, hK, hU0]
  | succ n ih =>
    intro x
    rw [hFrec, hUrec, exponential_causal_convolution_factorisation]
    congr 1
    funext s
    rw [hK, ih]
