-- Prove2me | solution 1 for GDGen3.total_sub_suffix
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:04:06.634988+00:00
-- url     : https://prove2.me/submissions/db2f33b0-c153-4cd0-bc6f-eec31be9c478

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_prefix_indicator

noncomputable section

open Finset

open GDGen3

theorem solution (F : ℕ → ℝ) (N a : ℕ) (ha : a ≤ N) :
    (∑ i ∈ range (N + 1), F i) - (∑ i ∈ range (N + 1), if a < i then F i else 0)
      = ∑ i ∈ range (a + 1), F i := by
  rw [← sum_sub_distrib, ← sum_prefix_indicator F (N + 1) (a + 1) (by omega)]
  apply sum_congr rfl
  intro i hi
  by_cases h : a < i
  · simp [h, show ¬i < a + 1 by omega]
  · simp [h, show i < a + 1 by omega]
