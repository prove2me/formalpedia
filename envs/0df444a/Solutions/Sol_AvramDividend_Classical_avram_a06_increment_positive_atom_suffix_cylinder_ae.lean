-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_increment_positive_atom_suffix_cylinder_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:50:22.066409+00:00
-- url     : https://prove2.me/submissions/65f93d5c-274e-48b1-8b79-f23eed6c6d7c

import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_increment_suffix_threshold_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Positive increment singleton cylinder via two successive suffix thresholds. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    ∀ᵐ ω ∂P, ∀ (v : ℝ) (m : ℕ),
      N ω (clock + v) - N ω clock = m + 1 ↔
        (τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) +
          (∑ j ∈ Finset.range m, τ (N ω clock + 1 + j) ω) ≤ v ∧
         v < τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) +
          (∑ j ∈ Finset.range (m + 1), τ (N ω clock + 1 + j) ω)) := by
  filter_upwards [
    AvramDividend.Classical.avram_a06_count_increment_suffix_threshold_ae
      P τ N hThreshold clock] with ω hω
  intro v m
  have hLow := hω v m
  have hHigh := hω v (m + 1)
  constructor
  · intro heq
    have h₁ : m < N ω (clock + v) - N ω clock := by omega
    have h₂ : ¬ (m + 1 < N ω (clock + v) - N ω clock) := by omega
    refine ⟨hLow.mp h₁, ?_⟩
    have hn : ¬ (τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) +
        (∑ j ∈ Finset.range (m + 1), τ (N ω clock + 1 + j) ω) ≤ v) := by
      intro hp
      exact h₂ (hHigh.mpr hp)
    exact lt_of_not_ge hn
  · rintro ⟨h₁, h₂⟩
    have ha : m < N ω (clock + v) - N ω clock := hLow.mpr h₁
    have hb : ¬ (m + 1 < N ω (clock + v) - N ω clock) := by
      intro hc
      exact (not_le_of_gt h₂) (hHigh.mp hc)
    omega
