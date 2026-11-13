-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_grid_eventually_beyond_strict_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:31:13.907808+00:00
-- url     : https://prove2.me/submissions/6ac42792-b78b-4b88-a1cd-ea0c0ec764ba

import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Archimedean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

theorem solution (n r : ℝ) (hr0 : 0 ≤ r) (hrn : r < n) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      r ≤ (m : ℝ) * (n / ((m : ℝ) + 1)) := by
  have hd : 0 < n - r := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (r / (n - r))
  refine ⟨k, ?_⟩
  intro m hm
  have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hk' : r < (k : ℝ) * (n - r) :=
    (div_lt_iff₀ hd).mp hk
  have hmon : (k : ℝ) * (n - r) ≤ (m : ℝ) * (n - r) :=
    mul_le_mul_of_nonneg_right hkm (le_of_lt hd)
  have hmain : r ≤ (m : ℝ) * (n - r) :=
    (le_of_lt hk').trans hmon
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmul : r * ((m : ℝ) + 1) ≤ (m : ℝ) * n := by
    nlinarith [hmain]
  calc
    r ≤ ((m : ℝ) * n) / ((m : ℝ) + 1) :=
      (le_div_iff₀ hden).mpr hmul
    _ = (m : ℝ) * (n / ((m : ℝ) + 1)) := by ring
