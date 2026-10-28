-- Prove2me | solution 1 for AvramDividend.Classical.causal_renewal_density_interval_integrable_away_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:31:35.920182+00:00
-- url     : https://prove2.me/submissions/64e44612-c0f0-420b-abac-70c36f1256ca

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hκint : Integrable κ volume)
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun y : ℝ => ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else F (n - 1) y) volume a b := by
  have hc := AvramDividend.Classical.causal_renewal_density_continuous_of_convolution_bounds
    κ F ρ hρ0 hρ1 hκint hκcont hκzero hκbound hF0 hFsucc hFnonneg hFpoint
  refine ContinuousOn.intervalIntegrable (hc.mono ?_)
  rw [uIcc_of_le hab]
  exact fun y hy => lt_of_lt_of_le ha hy.1
