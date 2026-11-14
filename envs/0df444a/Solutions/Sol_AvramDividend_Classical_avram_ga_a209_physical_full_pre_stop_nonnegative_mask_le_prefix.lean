-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a209_physical_full_pre_stop_nonnegative_mask_le_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:30:45.32121+00:00
-- url     : https://prove2.me/submissions/60581b2b-bd76-481e-af86-abb0ab9c059b

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.NNReal.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

/-- Full stopping cells form a subset of prefix stopping cells. -/
theorem solution
    {Ω : Type*} (m : ℕ) (s : ℕ → ℝ≥0)
    (Δ : ℝ≥0) (ρ : Ω → ℝ≥0) (f : ℕ → Ω → ℝ)
    (hf : ∀ i ω, 0 ≤ f i ω) (ω : Ω) :
    (∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then f i ω else 0) ≤
    (∑ i ∈ Finset.range m,
      if s i < ρ ω then f i ω else 0) := by
  apply Finset.sum_le_sum
  intro i _
  by_cases h : s i < ρ ω ∧ s i + Δ ≤ ρ ω
  · simp [h, h.1]
  · by_cases hs : s i < ρ ω
    · simpa only [if_neg h, if_pos hs] using hf i ω
    · simp [h, hs]
