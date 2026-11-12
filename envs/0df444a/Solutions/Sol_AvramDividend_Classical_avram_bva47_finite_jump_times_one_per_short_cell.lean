-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva47_finite_jump_times_one_per_short_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:08:19.785637+00:00
-- url     : https://prove2.me/submissions/13c3c718-d53b-43d8-a911-2c98b94aca64

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva41_finite_distinct_mark_times_positive_gap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- A sufficiently short half-open time cell contains at most one marked jump time. -/
theorem solution (S : Finset ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ a s t : ℝ, s ∈ S → t ∈ S →
        a ≤ s → s < a + δ → a ≤ t → t < a + δ → s = t := by
  obtain ⟨δ, hδ, hsep⟩ :=
    avram_bva41_finite_distinct_mark_times_positive_gap S
  refine ⟨δ, hδ, ?_⟩
  intro a s t hs ht hsa hsa' hta hta'
  by_contra hne
  have hd := hsep s hs t ht hne
  have hlt : |s - t| < δ := by
    apply abs_lt.mpr
    constructor <;> linarith
  linarith
