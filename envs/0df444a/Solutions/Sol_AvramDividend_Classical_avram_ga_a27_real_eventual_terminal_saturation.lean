-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_real_eventual_terminal_saturation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:29:40.99107+00:00
-- url     : https://prove2.me/submissions/9d8a7a02-dea5-4ce6-a496-c472dfb17b24

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

theorem solution
    (r n : ℝ) (hn : r < n) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      r ≤ (m : ℝ) * n / ((m : ℝ) + 1) := by
  have hgap : 0 < n - r := sub_pos.mpr hn
  obtain ⟨k, hk⟩ := exists_nat_gt (r / (n - r))
  refine ⟨k, ?_⟩
  intro m hm
  have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ht : r / (n - r) < (m : ℝ) := lt_of_lt_of_le hk hkm
  have hb : r < (m : ℝ) * (n - r) := (div_lt_iff₀ hgap).mp ht
  have hden : 0 < (m : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith
