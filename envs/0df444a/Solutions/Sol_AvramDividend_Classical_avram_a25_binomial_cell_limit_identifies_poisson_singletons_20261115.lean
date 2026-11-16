-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_binomial_cell_limit_identifies_poisson_singletons_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:25:07.523206+00:00
-- url     : https://prove2.me/submissions/23766880-6002-479d-a1eb-f826a79953a8

import Mathlib
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- The rare-cell binomial limit uniquely identifies a Poisson count law. -/
theorem solution
    (μ : Measure ℕ) (r : ℝ≥0) (p : ℕ → unitInterval)
    (hRate : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ))
      atTop (𝓝 (r : ℝ)))
    (hApprox : ∀ k : ℕ,
      Tendsto (fun n : ℕ => Bin(n, p n) {k})
        atTop (𝓝 (μ {k}))) :
    ∀ k : ℕ, μ {k} = poissonMeasure r {k} := by
  intro k
  have hPoisson :
      Tendsto (fun n : ℕ => Bin(n, p n) {k})
        atTop (𝓝 (poissonMeasure r {k})) :=
    binomial_tendsto_poissonPMFReal_atTop k hRate
  exact tendsto_nhds_unique (hApprox k) hPoisson
