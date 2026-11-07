-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_bounded_clock_min_nat_stopping_and_exact_payoff_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:42:48.544686+00:00
-- url     : https://prove2.me/submissions/b7535aba-d05c-47ee-b4b7-348ef3b7ba4b

import Mathlib.Probability.Process.Stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section
/-- A finite original stopping horizon can be exhausted by deterministic
clipping while preserving the *same* exact physical stopped payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (n : ℕ)
    (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (hStop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (Pay : ℝ≥0 → Ω → ℝ) :
    (∀ k : ℕ, IsStoppingTime 𝓕
      (fun ω => ((min (τ ω) (k : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0))) ∧
    (∀ k : ℕ, ∀ ω, min (τ ω) (k : ℝ≥0) ≤ τ ω) ∧
    (∀ ω, ∀ᶠ k : ℕ in Filter.atTop,
      min (τ ω) (k : ℝ≥0) = τ ω) ∧
    (∀ ω, Filter.Tendsto
      (fun k : ℕ => ENNReal.ofReal (Pay (min (τ ω) (k : ℝ≥0)) ω))
      Filter.atTop (nhds (ENNReal.ofReal (Pay (τ ω) ω)))) := by
  have hStops : ∀ k : ℕ, IsStoppingTime 𝓕
      (fun ω => ((min (τ ω) (k : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)) := by
    intro k
    simpa only [WithTop.coe_min] using
      (hStop.min_const (k : ℝ≥0))
  have hLower : ∀ k : ℕ, ∀ ω, min (τ ω) (k : ℝ≥0) ≤ τ ω := by
    intro k ω
    exact min_le_left _ _
  have hEventually : ∀ ω, ∀ᶠ k : ℕ in Filter.atTop,
      min (τ ω) (k : ℝ≥0) = τ ω := by
    intro ω
    filter_upwards [Filter.eventually_ge_atTop n] with k hk
    have hnk : (n : ℝ≥0) ≤ (k : ℝ≥0) := by exact_mod_cast hk
    exact min_eq_left ((hBound ω).trans hnk)
  refine ⟨hStops, hLower, hEventually, ?_⟩
  intro ω
  apply (tendsto_const_nhds : Filter.Tendsto
    (fun _ : ℕ => ENNReal.ofReal (Pay (τ ω) ω))
    Filter.atTop (nhds (ENNReal.ofReal (Pay (τ ω) ω)))).congr'
  filter_upwards [hEventually ω] with k hk
  simp only [hk]
