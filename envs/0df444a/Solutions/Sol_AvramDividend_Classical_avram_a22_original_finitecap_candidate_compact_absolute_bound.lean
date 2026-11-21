-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_finitecap_candidate_compact_absolute_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:22:44.83154+00:00
-- url     : https://prove2.me/submissions/e4b27b9d-ee46-43ba-91dc-5e653d166ed5

import Mathlib
open Set

theorem solution
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hcont : ContinuousOn w (Icc 0 b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ,
      0 ≤ z → z ≤ b → |w z| ≤ K  := by
  have hBound : BddAbove ((fun z : ℝ => |w z|) '' Icc 0 b) :=
    isCompact_Icc.bddAbove_image hcont.abs
  obtain ⟨K, hK⟩ := hBound
  refine ⟨max K 0, le_max_right K 0, ?_⟩
  intro z hz0 hzb
  have hz : z ∈ Icc 0 b := ⟨hz0, hzb⟩
  have hzK : |w z| ≤ K := hK (Set.mem_image_of_mem _ hz)
  exact le_trans hzK (le_max_left K 0)
