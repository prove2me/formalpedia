-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_arbitrary_cofinal_bands_cover_each_fixed_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:56:28.517+00:00
-- url     : https://prove2.me/submissions/3195ff80-f8a2-43cb-b04c-e20eab150cde

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hcC : ENNReal.ofReal c < C) (hdC : ENNReal.ofReal d < C) :
    ∃ N : ℕ, ∀ n ≥ N, Icc c d ⊆ Icc (a n) (b n) := by
  obtain ⟨Nc, hNc⟩ := hcover c hc hcC
  obtain ⟨Nd, hNd⟩ := hcover d (lt_of_lt_of_le hc hcd) hdC
  refine ⟨max Nc Nd, ?_⟩
  intro n hn y hy
  have hcn := hNc n (le_trans (Nat.le_max_left Nc Nd) hn)
  have hdn := hNd n (le_trans (Nat.le_max_right Nc Nd) hn)
  exact ⟨le_trans hcn.1 hy.1, le_trans hy.2 hdn.2⟩
