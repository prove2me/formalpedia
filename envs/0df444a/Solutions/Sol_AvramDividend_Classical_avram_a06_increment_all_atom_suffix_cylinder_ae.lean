-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_increment_all_atom_suffix_cylinder_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:03:56.498193+00:00
-- url     : https://prove2.me/submissions/03700365-3fe4-4164-b6fb-e7b7b60c3fc6

import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_AvramDividend_Classical_avram_a06_increment_zero_atom_suffix_cylinder_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_increment_positive_atom_suffix_cylinder_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- The zero and positive count singleton events have a common null exceptional set. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    ∀ᵐ ω ∂P, ∀ (v : ℝ) (m : ℕ),
      N ω (clock + v) - N ω clock = m ↔
        if m = 0 then v < τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)
        else (τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) + (∑ j ∈ Finset.range (m - 1), τ (N ω clock + 1 + j) ω)) ≤ v ∧ v < (τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) + (∑ j ∈ Finset.range m, τ (N ω clock + 1 + j) ω)) := by
  filter_upwards [
    AvramDividend.Classical.avram_a06_increment_zero_atom_suffix_cylinder_ae
      P τ N hThreshold clock,
    AvramDividend.Classical.avram_a06_increment_positive_atom_suffix_cylinder_ae
      P τ N hThreshold clock] with ω hz hp
  intro v m
  cases m with
  | zero =>
      simpa using hz v
  | succ k =>
      simpa using hp v k
