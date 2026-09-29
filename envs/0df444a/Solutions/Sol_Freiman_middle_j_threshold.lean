-- Prove2me | solution 1 for Freiman.middle_j_threshold
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:32:51.772933+00:00
-- url     : https://prove2.me/submissions/efb25dec-f506-4839-ad6e-20d783bada4c

import Theorems.Thm_Freiman_middle_j_first_threshold
import Theorems.Thm_Freiman_middle_j_real_threshold_bounds
import Theorems.Thm_Freiman_middle_j_recurrence
import Theorems.Thm_Freiman_middle_j_tail_boxes

open Freiman

theorem solution :
    ∀ (p s : ℝ) (k : ℕ), p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) → 1 ≤ k → middleHStar p s < middleJThreshold p s k := by
  intro p s k hp hs hk
  by_cases h : k=1
  · subst k
    exact middle_j_first_threshold p s hp hs
  · exact middle_j_real_threshold_bounds middle_j_recurrence middle_j_tail_boxes p s k hp hs (by omega)
