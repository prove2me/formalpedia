-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:46:18.605302+00:00
-- url     : https://prove2.me/submissions/0cef6a60-b040-456d-94f2-b0280b7c4549

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_cofinal_mask_eventually_covers_finite_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (n : ℕ) (z : ℕ → ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ i < n + 1,
      (0 < z i ∧ ENNReal.ofReal (z i) < C) →
        z i ∈ Icc (a k) (b k) := by
  classical
  let s : Finset ℕ :=
    (Finset.range (n + 1)).filter
      (fun i => 0 < z i ∧ ENNReal.ofReal (z i) < C)
  have hS : ∀ i ∈ s, 0 < z i ∧ ENNReal.ofReal (z i) < C := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨N, hN⟩ :=
    avram_p3_grid4_turn13_cofinal_mask_eventually_covers_finite_grid
      C a b hExh s z hS
  refine ⟨N, ?_⟩
  intro k hk i hi hzi
  apply hN k hk i
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hzi⟩
