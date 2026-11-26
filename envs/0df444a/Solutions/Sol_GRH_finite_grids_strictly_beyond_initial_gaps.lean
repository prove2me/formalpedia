-- Prove2me | solution 1 for GRH.finite_grids_strictly_beyond_initial_gaps
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T16:19:37.978444+00:00
-- url     : https://prove2.me/submissions/cddc385b-978c-4b52-b19e-f6ebb80cc5b5

import Theorems.Thm_GRH_initial_gap_test_misses_large_primes_and_height_three
import Theorems.Thm_GRH_weighted_prefix_first_and_third_grids

/-- These passing finite grids satisfy the hypothesis that the former
initial-gap test fails, at both new levels and a new height. -/
theorem solution (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (h : ℕ) (hc : (h=0 ∧ d ∣ 42 ∧ 7 ∣ d) ∨ (h=2 ∧ d ∣ 6)) :
    (¬ GRH.DirichletPeriod.Covers d (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1)) ∧
    ∃ m : ℕ, GRH.DirichletGrid.Passes χ
      (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  constructor
  · apply GRH.initial_gap_test_misses_large_primes_and_height_three
    rcases hc with ⟨_,_,hd⟩ | ⟨rfl,_⟩
    · exact Or.inl ⟨7,by decide,le_rfl,hd⟩
    · exact Or.inr le_rfl
  · apply GRH.weighted_prefix_first_and_third_grids d χ hχ h
    rcases hc with ⟨hh,hd,_⟩ | rest
    · exact Or.inl ⟨hh, Or.inr (Or.inr (Or.inl hd))⟩
    · exact Or.inr rest
