-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_laplace_resolvent_series
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:31:00.692105+00:00
-- url     : https://prove2.me/submissions/d7bd21fc-2630-4661-a5be-018f72525db9

import Theorems.Thm_AvramDividend_Classical_causal_geometric_laplace_series_integral
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open AvramDividend.Classical MeasureTheory Set
theorem solution
    (F : ℕ → ℝ → ℝ) (θ ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * F n x)
      (Ioi (0 : ℝ)) volume)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * F n x ∂volume) =
        ρ ^ (n + 1)) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * (∑' n : ℕ, F n x) ∂volume) =
        ρ / (1 - ρ) := by 
  simp_rw [← tsum_mul_left]
  exact causal_geometric_laplace_series_integral F θ ρ hρ0 hρ1 hFi hpos hmass
