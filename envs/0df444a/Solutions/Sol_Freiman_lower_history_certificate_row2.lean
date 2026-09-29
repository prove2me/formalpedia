-- Prove2me | solution 1 for Freiman.lower_history_certificate_row2
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:27.907014+00:00
-- url     : https://prove2.me/submissions/5df27bdb-84bc-4afa-854c-362a352eac9d

import Theorems.Thm_Freiman_lowerHistory_hazard_target

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (hw : lowerBoundedHistory h n) :
    ¬ lowerMixed (h n) → ¬ lowerA (h n) 3 → lowerRStar (h n) → lowerLocalLower (h n) ([2],[2]) ≤ lowerLocalCoordinate (h n) t := by
  intro hm ha hs
  have ht := lowerHistory_hazard_target t h n 2 hh (by simp) ⟨hm,ha,hs⟩
  exact ht
