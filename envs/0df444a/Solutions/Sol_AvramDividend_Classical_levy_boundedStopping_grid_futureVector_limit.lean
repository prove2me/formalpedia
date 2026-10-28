-- Prove2me | solution 1 for AvramDividend.Classical.levy_boundedStopping_grid_futureVector_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:06:38.833681+00:00
-- url     : https://prove2.me/submissions/c7ba1778-7cbf-4032-83be-34aebaf28122

import Mathlib.Topology.Constructions
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
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    ∃ (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0),
      (∀ n ω, τn n ω ∈ grid n) ∧
      (∀ n s, s ∈ grid n →
        MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
      (∀ ω n, τ ω ≤ τn n ω) ∧
      (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) ∧
      (∀ J : Finset ℝ≥0, ∀ ω : Ω,
        Tendsto
          (fun n : ℕ => fun j : J =>
            X.X (τn n ω + (j : ℝ≥0)) ω - X.X (τn n ω) ω)
          atTop
          (𝓝 (fun j : J =>
            X.X (τ ω + (j : ℝ≥0)) ω - X.X (τ ω) ω))) := by
  obtain ⟨τn, grid, h1, h2, h3, h4⟩ :=
    AvramDividend.Classical.bounded_stopping_dyadic_grid_approximation 𝓕 τ hstop T hbound
  exact ⟨τn, grid, h1, h2, h3, h4, fun J ω => tendsto_pi_nhds.2 fun j =>
    AvramDividend.Classical.chat08_stopped_levy_increment_tendsto_of_right_approximation X τn τ j h4 h3 ω⟩
