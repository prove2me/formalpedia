-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_stoppedEvent_horizon_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:10:41.84315+00:00
-- url     : https://prove2.me/submissions/dd679823-8f30-428d-a5a6-76086c1759fd

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Algebra.Order.Archimedean.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Discounted rewards on finite-horizon stopped events converge to the full stopped event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Ω → ℝ≥0) (A : Set Ω)
    (f : Ω → ℝ≥0∞)
    (hMeas : ∀ n : ℕ,
      Measurable (Set.indicator
        (A ∩ {ω : Ω | τ ω ≤ (n : ℝ≥0)}) f))
    (C : ℝ≥0∞) (hBound : ∀ ω, f ω ≤ C)
    (hFinite : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    Tendsto
      (fun n : ℕ => ∫⁻ ω, Set.indicator
        (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)}) f ω ∂P)
      atTop
      (nhds (∫⁻ ω, Set.indicator A f ω ∂P)) := by
  refine tendsto_lintegral_of_dominated_convergence
    (μ := P) (fun _ : Ω => C) hMeas ?_ hFinite ?_
  · intro n
    filter_upwards [] with ω
    by_cases hω : ω ∈ (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)})
    · simpa [Set.indicator, hω] using hBound ω
    · simp [Set.indicator, hω]
  · filter_upwards [] with ω
    obtain ⟨N, hN⟩ : ∃ N : ℕ, τ ω ≤ (N : ℝ≥0) :=
      exists_nat_ge (τ ω)
    have hEq :
        (fun n : ℕ => Set.indicator
          (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)}) f ω) =ᶠ[atTop]
        (fun _ : ℕ => Set.indicator A f ω) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ≥0) ≤ (n : ℝ≥0) := by
        exact_mod_cast hn
      have hτn : τ ω ≤ (n : ℝ≥0) := hN.trans hcast
      by_cases hA : ω ∈ A
      · simp [Set.indicator, hA, hτn]
      · simp [Set.indicator, hA]
    exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
