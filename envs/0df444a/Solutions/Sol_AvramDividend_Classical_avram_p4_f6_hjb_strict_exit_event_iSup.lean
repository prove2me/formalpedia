-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_hjb_strict_exit_event_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:18:46.163087+00:00
-- url     : https://prove2.me/submissions/fb64ad43-803d-4333-820b-80bab963f292

import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal
noncomputable section

theorem solution (u d v : ℝ≥0∞) :
    (⨆ n : ℕ, if u < d ∧ u ≤ (n : ℝ≥0∞) then v else 0) =
      (if u < d then v else 0) := by
  by_cases h : u < d
  · simp only [if_pos h]
    have hu : u ≠ ⊤ := (lt_of_lt_of_le h le_top).ne
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hu
    apply le_antisymm
    · apply iSup_le
      intro k
      by_cases hk : u ≤ (k : ℝ≥0∞)
      · simp [h, hk]
      · simp [h, hk]
    · have hmem : u < d ∧ u ≤ (n : ℝ≥0∞) := ⟨h, le_of_lt hn⟩
      calc
        v = (if u < d ∧ u ≤ (n : ℝ≥0∞) then v else 0) := by simp [hmem]
        _ ≤ ⨆ k : ℕ, (if u < d ∧ u ≤ (k : ℝ≥0∞) then v else 0) :=
          le_iSup (fun k : ℕ => if u < d ∧ u ≤ (k : ℝ≥0∞) then v else 0) n
  · simp [h]
