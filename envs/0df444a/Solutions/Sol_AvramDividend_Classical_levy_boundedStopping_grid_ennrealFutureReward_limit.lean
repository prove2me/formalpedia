-- Prove2me | solution 1 for AvramDividend.Classical.levy_boundedStopping_grid_ennrealFutureReward_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:12:03.675742+00:00
-- url     : https://prove2.me/submissions/df2b2cf9-5d2d-4b6f-b0f2-0963de33aa4e

import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_wholeFuturePath_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Continuous nonnegative future rewards converge along finite adapted stopping grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Continuous g) :
    ∃ (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0),
      (∀ n ω, τn n ω ∈ grid n) ∧
      (∀ n s, s ∈ grid n →
        MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
      (∀ ω n, τ ω ≤ τn n ω) ∧
      (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) ∧
      (∀ ω : Ω,
        Tendsto
          (fun n : ℕ => g (fun t : ℝ≥0 =>
            X.X (τn n ω + t) ω - X.X (τn n ω) ω))
          atTop
          (𝓝 (g (fun t : ℝ≥0 =>
            X.X (τ ω + t) ω - X.X (τ ω) ω)))) := by
  obtain ⟨τn, grid, hgrid, hfib, habove, hconv, hpath⟩ :=
    levy_boundedStopping_grid_wholeFuturePath_limit X τ hstop T hbound
  refine ⟨τn, grid, hgrid, hfib, habove, hconv, ?_⟩
  intro ω
  exact (hg.tendsto _).comp (hpath ω)