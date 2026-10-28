-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_power_series_exact_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:30:45.666295+00:00
-- url     : https://prove2.me/submissions/a83f1539-1e83-4ed1-9f7f-4fec5d2213bb

import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_laplace_geometric
import Theorems.Thm_AvramDividend_Classical_causal_geometric_laplace_resolvent_series
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Exact Laplace transform of a nonnegative causal renewal series from its kernel data alone. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (θ ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hκi : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * κ t)
      (Ioi (0 : ℝ)) volume)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) = fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hκmass : (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * κ t ∂volume) = ρ) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * (∑' n : ℕ, F n x) ∂volume) =
        ρ / (1 - ρ) := by
  have hFi :=
    causal_convolution_powers_weighted_integrable κ F θ hκi hF0 hFsucc
  have hmasses :=
    causal_convolution_powers_laplace_geometric
      κ F θ ρ hκi hFi hF0 hFsucc hκmass
  exact causal_geometric_laplace_resolvent_series
    F θ ρ hρ0 hρ1 hFi hFpos hmasses
