-- Prove2me | solution 2 for AvramDividend.Classical.canonical_drifted_brownian_cadlag_no_positive_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:36:53.972988+00:00
-- url     : https://prove2.me/submissions/dcf59fcd-ac86-45a3-82fe-57fbcbb329e7

import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_zero_continuous
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  dsimp only
  have hc := (AvramDividend.Classical.canonical_drifted_brownian_zero_continuous ω).2
  refine ⟨fun t => hc.continuousAt.continuousWithinAt,
      fun t _ => ⟨_, (hc.tendsto t).mono_left inf_le_left⟩, ?_⟩
  intro t l ht hl
  haveI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hcont : Tendsto (fun s : ℝ≥0 =>
       ProbabilityTheory.brownian s ω - ProbabilityTheory.brownian 0 ω - (s : ℝ))
       (𝓝[<] t)
       (𝓝 (ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω - (t : ℝ))) :=
    (hc.tendsto t).mono_left inf_le_left
  exact le_of_eq (tendsto_nhds_unique hcont hl)
