-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_strict_cofinal_rows_never_contain_upper_cap_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:35:01.074079+00:00
-- url     : https://prove2.me/submissions/cf692a8f-546a-48f6-b9c1-330be09b52db

import Mathlib.Data.ENNReal.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set
open scoped ENNReal
noncomputable section

/-- The original strict spatial band omits the upper cap on every row. -/
theorem solution
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n : ℕ) (y : ℝ) (hcap : ENNReal.ofReal y = C) :
    y ∉ Icc (a n) (b n) := by
  intro hy
  have hhalf : y ∈ Icc (a n / 2) (b n) := by
    exact ⟨by linarith [ha n, hy.1], hy.2⟩
  have hlt : ENNReal.ofReal y < C := (hinside n hhalf).2
  rw [hcap] at hlt
  exact (lt_irrefl C) hlt
