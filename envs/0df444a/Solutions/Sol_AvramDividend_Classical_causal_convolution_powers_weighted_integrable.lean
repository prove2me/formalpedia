-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_powers_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:47:22.637987+00:00
-- url     : https://prove2.me/submissions/bb513ac4-0dcf-48f1-a45d-1c3ef317c7b3

import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
open AvramDividend.Classical MeasureTheory Set
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (θ : ℝ)
    (hκi : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * κ t)
      (Ioi (0 : ℝ)) volume)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) = fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume) :
    ∀ n : ℕ, IntegrableOn
      (fun t : ℝ => Real.exp (-(θ * t)) * F n t)
      (Ioi (0 : ℝ)) volume := by 
  intro n
  induction n with
  | zero => rw [hF0]; exact hκi
  | succ n ih =>
    rw [hFsucc n]
    exact positive_causal_convolution_laplace_integrable κ (F n) θ hκi ih
