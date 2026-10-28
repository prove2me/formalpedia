-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_weighted_series_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:27:34.99231+00:00
-- url     : https://prove2.me/submissions/529bd838-b301-492d-bd99-e261003f11bc

import Theorems.Thm_AvramDividend_Classical_causal_geometric_weighted_tsum_integrable
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Put the exponential weight outside an integrable positive renewal sum. -/
theorem solution
    (F : ℕ → ℝ → ℝ) (θ ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * F n x)
      (Ioi (0 : ℝ)) volume)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hpoint : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * F n x ∂volume) =
        ρ ^ (n + 1)) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * (∑' n : ℕ, F n x))
      (Ioi (0 : ℝ)) volume := by
  have hweighted (x : ℝ) :
      Summable (fun n : ℕ => Real.exp (-(θ * x)) * F n x) :=
    (hpoint x).mul_left _
  have hi :=
    causal_geometric_weighted_tsum_integrable
      F θ ρ hρ0 hρ1 hFi hpos hweighted hmass
  simpa only [← tsum_mul_left] using hi
