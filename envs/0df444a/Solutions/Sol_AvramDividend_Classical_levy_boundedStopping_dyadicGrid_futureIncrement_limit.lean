-- Prove2me | solution 1 for AvramDividend.Classical.levy_boundedStopping_dyadicGrid_futureIncrement_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:02:49.414569+00:00
-- url     : https://prove2.me/submissions/f4b76859-b39d-4699-a90b-0c100edb5528

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stopping_dyadic_grid_approximation
import Theorems.Thm_AvramDividend_Classical_chat08_stopped_levy_increment_tendsto_of_right_approximation

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) (u : ℝ≥0) :
    ∃ (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0),
      (∀ n ω, τn n ω ∈ grid n) ∧
      (∀ n s, s ∈ grid n →
        MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
      (∀ ω n, τ ω ≤ τn n ω) ∧
      (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) ∧
      (∀ ω, Tendsto
        (fun n => X.X (τn n ω + u) ω - X.X (τn n ω) ω)
        atTop (𝓝 (X.X (τ ω + u) ω - X.X (τ ω) ω))) := by
  obtain ⟨τn, grid, h1, h2, h3, h4⟩ :=
    AvramDividend.Classical.bounded_stopping_dyadic_grid_approximation 𝓕 τ hstop T hbound
  exact ⟨τn, grid, h1, h2, h3, h4,
    AvramDividend.Classical.chat08_stopped_levy_increment_tendsto_of_right_approximation X τn τ u h4 h3⟩
