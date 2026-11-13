-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB193_select_level_avoiding_countable_null_occupations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:41:54.43817+00:00
-- url     : https://prove2.me/submissions/431a1048-906e-428a-aba5-5146fb8ff456

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB192_choose_good_clipping_level_outside_null_set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    (S : ℕ → Set ℝ)
    (hS : ∀ k, (volume : Measure ℝ) (S k) = 0)
    (a b : ℝ) (hab : a < b) :
    ∃ z : ℝ, z ∈ Ioo a b ∧ ∀ k, z ∉ S k := by
  have hnull : (volume : Measure ℝ) (⋃ k, S k) = 0 :=
    measure_iUnion_null hS
  obtain ⟨z, hz, hnot⟩ :=
    avram_gbB192_choose_good_clipping_level_outside_null_set
      (⋃ k, S k) hnull a b hab
  refine ⟨z, hz, ?_⟩
  intro k hk
  exact hnot (Set.mem_iUnion.mpr ⟨k, hk⟩)
