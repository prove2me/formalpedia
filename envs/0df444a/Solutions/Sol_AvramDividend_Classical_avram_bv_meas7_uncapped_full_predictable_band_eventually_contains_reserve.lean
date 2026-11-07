-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_uncapped_full_predictable_band_eventually_contains_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:50:51.934827+00:00
-- url     : https://prove2.me/submissions/a2a80222-89c7-4363-b86d-9efdb7479d69

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uncapped_band_eventually_contains_positive_reserve
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
noncomputable section

/-- Every fixed positive original reserve eventually lies in the full
uncapped predictable pre-reserve band [a_n,b_n], not only [a_n/2,b_n]. -/
theorem solution (y : ℝ) (hy : 0 < y) :
    ∃ N : ℕ, ∀ n ≥ N,
      y ∈ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) := by
  have hyhalf : 0 < y / 2 := by linarith
  obtain ⟨Nlo, hNlo⟩ :=
    avram_p3_grid4_uncapped_band_eventually_contains_positive_reserve
      (y / 2) hyhalf
  obtain ⟨Nhi, hNhi⟩ :=
    avram_p3_grid4_uncapped_band_eventually_contains_positive_reserve y hy
  refine ⟨max Nlo Nhi, ?_⟩
  intro n hn
  have hnlo : Nlo ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnhi : Nhi ≤ n := le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hlo, _⟩ := hNlo n hnlo
  obtain ⟨_, hhi⟩ := hNhi n hnhi
  change 1 / ((n : ℝ) + 1) ≤ y ∧ y ≤ (n : ℝ) + 2
  constructor
  · have hlower : (1 / ((n : ℝ) + 1)) / 2 ≤ y / 2 := hlo
    linarith
  · exact hhi
