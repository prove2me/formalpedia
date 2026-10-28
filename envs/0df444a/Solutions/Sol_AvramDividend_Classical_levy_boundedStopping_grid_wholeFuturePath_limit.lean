-- Prove2me | solution 1 for AvramDividend.Classical.levy_boundedStopping_grid_wholeFuturePath_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:15:46.676305+00:00
-- url     : https://prove2.me/submissions/17b847b1-4167-4014-9a37-3400f019ffaf

import Mathlib.Topology.Constructions
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stopping_dyadic_grid_approximation
import Theorems.Thm_AvramDividend_Classical_chat08_stopped_levy_increment_tendsto_of_right_approximation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- One adapted grid converges to the entire future Lévy path in product topology. -/
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
      (∀ ω : Ω,
        Tendsto
          (fun n : ℕ => fun t : ℝ≥0 =>
            X.X (τn n ω + t) ω - X.X (τn n ω) ω)
          atTop
          (𝓝 (fun t : ℝ≥0 =>
            X.X (τ ω + t) ω - X.X (τ ω) ω))) := by
  obtain ⟨τn, grid, hgrid, hfibres, habove, hconv⟩ :=
    bounded_stopping_dyadic_grid_approximation 𝓕 τ hstop T hbound
  refine ⟨τn, grid, hgrid, hfibres, habove, hconv, ?_⟩
  intro ω
  apply tendsto_pi_nhds.mpr
  intro t
  exact chat08_stopped_levy_increment_tendsto_of_right_approximation
    X τn τ t hconv habove ω
