-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_nnreal_eventual_terminal_saturation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:41:58.978195+00:00
-- url     : https://prove2.me/submissions/5561f608-8fe9-44bb-b18f-6fabd5c04590

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

theorem solution
    (r n : ℝ≥0) (hr : r < n) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      r ≤ (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)) := by
  have hr' : (r : ℝ) < (n : ℝ) := by exact_mod_cast hr
  have hgap : 0 < (n : ℝ) - (r : ℝ) := sub_pos.mpr hr'
  obtain ⟨k, hk⟩ := exists_nat_gt ((r : ℝ) / ((n : ℝ) - (r : ℝ)))
  refine ⟨k, ?_⟩
  intro m hm
  have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ht : (r : ℝ) / ((n : ℝ) - (r : ℝ)) < (m : ℝ) :=
    lt_of_lt_of_le hk hkm
  have hb : (r : ℝ) < (m : ℝ) * ((n : ℝ) - (r : ℝ)) :=
    (div_lt_iff₀ hgap).mp ht
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hreal : (r : ℝ) ≤ (m : ℝ) * (n : ℝ) / ((m : ℝ) + 1) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hnnreal : r ≤ (m : ℝ≥0) * n / ((m : ℝ≥0) + 1) := by exact_mod_cast hreal
  simpa only [mul_div_assoc] using hnnreal
