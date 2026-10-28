-- Prove2me | solution 2 for AvramDividend.Classical.causal_renewal_truncated_primitive_deriv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:56:20.987999+00:00
-- url     : https://prove2.me/submissions/e83fcbc8-3a74-4cdf-99c0-8334fd244b1d

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_interval_integrable_away_zero

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
    (a x : ℝ) (ha : 0 < a) (hax : a ≤ x) :
    deriv (fun b : ℝ =>
      ∫ y in a..b, (∑' n : ℕ,
        if n = 0 then (0 : ℝ) else F (n - 1) y)) x =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) x := by
  have hc := AvramDividend.Classical.causal_renewal_density_continuous_of_convolution_bounds
    κ F ρ hρ0 hρ1 hκint hκcont hκzero hκbound hF0 hFsucc hFnonneg hFpoint
  have hi := AvramDividend.Classical.causal_renewal_density_interval_integrable_away_zero
    κ F ρ hρ0 hρ1 hκint hκcont hκzero hκbound hF0 hFsucc hFnonneg hFpoint a x ha hax
  have hx : 0 < x := lt_of_lt_of_le ha hax
  exact (integral_hasDerivAt_right hi
    (hc.stronglyMeasurableAtFilter isOpen_Ioi x hx)
    (hc.continuousAt (Ioi_mem_nhds hx))).deriv
