-- Prove2me | solution 1 for AvramDividend.Classical.causal_renormalised_resolvent_laplace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:21:56.913698+00:00
-- url     : https://prove2.me/submissions/0c5659f3-3608-4373-a0d2-9865c0d4dfa8

import Theorems.Thm_AvramDividend_Classical_causal_convolution_power_series_exact_laplace
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Complex.Exponential
open AvramDividend.Classical MeasureTheory Set
theorem solution
    (K : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (θ η q ψ : ℝ)
    (hq : 0 < q) (hψ : q < ψ)
    (hKi : IntegrableOn
      (fun x : ℝ => Real.exp (-((η - θ) * x)) * K x)
      (Ioi (0 : ℝ)) volume)
    (hF0 : F 0 = K)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        K s * F n (x - s) ∂volume)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hKmass : (∫ x in Ioi (0 : ℝ),
      Real.exp (-((η - θ) * x)) * K x ∂volume) = q / ψ) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(η * x)) *
        ((Real.exp (θ * x) / q) * (∑' n : ℕ, F n x)) ∂volume) =
      1 / (ψ - q) := by 
  have hψ0 : 0 < ψ := by linarith
  have h := causal_convolution_power_series_exact_laplace K F (η - θ) (q / ψ)
    (by positivity) ((div_lt_one hψ0).mpr hψ) hKi hF0 hFsucc hFpos hKmass
  have e : (fun x : ℝ => Real.exp (-(η * x)) *
      ((Real.exp (θ * x) / q) * (∑' n : ℕ, F n x))) =
      fun x => (1 / q) * (Real.exp (-((η - θ) * x)) * (∑' n : ℕ, F n x)) := by
    ext x
    have : Real.exp (-(η * x)) * Real.exp (θ * x) = Real.exp (-((η - θ) * x)) := by
      rw [← Real.exp_add]; ring_nf
    rw [← this]; field_simp
  rw [e, integral_const_mul, h]
  have hq0 : q ≠ 0 := hq.ne'
  have : ψ - q ≠ 0 := by linarith
  field_simp
