-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a93_original_gaussian_stopped_full_cross_post_partition_finite_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:05:58.733753+00:00
-- url     : https://prove2.me/submissions/139c504b-3466-4cee-88e0-4b0b6cd34f29

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal

/-- The actual Gaussian stopped physical grid separates into full pre-stop cells, genuine crossing cells and identically zero post-stop cells. -/
theorem solution
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ ρ : ℝ≥0)
    (U F C : ℕ → ℝ)
    (hFull : ∀ i, s i < ρ → s i + Δ ≤ ρ → U i = F i)
    (hCross : ∀ i, s i < ρ → ρ < s i + Δ → U i = C i)
    (hPost : ∀ i, ρ ≤ s i → U i = 0) :
    (∑ i ∈ S, U i) =
      (∑ i ∈ S, if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0) +
      (∑ i ∈ S, if s i < ρ ∧ ρ < s i + Δ then C i else 0) := by
  classical
  calc
    (∑ i ∈ S, U i) =
        ∑ i ∈ S, ((if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0) +
          (if s i < ρ ∧ ρ < s i + Δ then C i else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hs : s i < ρ
      · by_cases he : s i + Δ ≤ ρ
        · have hn : ¬ ρ < s i + Δ := not_lt.mpr he
          simpa [hs, he, hn] using hFull i hs he
        · have hc : ρ < s i + Δ := lt_of_not_ge he
          simpa [hs, he, hc] using hCross i hs hc
      · have hp : ρ ≤ s i := le_of_not_gt hs
        simpa [hs] using hPost i hp
    _ = (∑ i ∈ S, if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0) +
        (∑ i ∈ S, if s i < ρ ∧ ρ < s i + Δ then C i else 0) := by
      exact Finset.sum_add_distrib
