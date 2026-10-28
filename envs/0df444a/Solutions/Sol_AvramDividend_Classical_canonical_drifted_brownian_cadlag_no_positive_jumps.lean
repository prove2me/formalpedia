-- Prove2me | solution 1 for AvramDividend.Classical.canonical_drifted_brownian_cadlag_no_positive_jumps
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:36:38.217602+00:00
-- url     : https://prove2.me/submissions/cb67c360-0b36-40e6-9352-45367a7fd323

import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_zero_continuous
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

open ProbabilityTheory MeasureTheory Filter Set Topology
open scoped NNReal

theorem solution
    (ω : ℝ≥0 → ℝ) :
    let X : ℝ≥0 → ℝ := fun t =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω - (t : ℝ)
    (∀ t : ℝ≥0, ContinuousWithinAt X (Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ, Tendsto X (𝓝[<] t) (𝓝 l)) ∧
    (∀ (t : ℝ≥0) (l : ℝ), 0 < t →
       Tendsto X (𝓝[<] t) (𝓝 l) → X t ≤ l) := by
  intro X
  have hc : Continuous X := (AvramDividend.Classical.canonical_drifted_brownian_zero_continuous ω).2
  refine ⟨fun t => hc.continuousWithinAt, fun t _ => ⟨X t, (hc.tendsto t).mono_left nhdsWithin_le_nhds⟩,
    fun t l ht h => ?_⟩
  have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  exact le_of_eq (tendsto_nhds_unique ((hc.tendsto t).mono_left nhdsWithin_le_nhds) h)
