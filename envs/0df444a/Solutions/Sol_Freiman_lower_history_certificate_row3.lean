-- Prove2me | solution 1 for Freiman.lower_history_certificate_row3
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:41.177587+00:00
-- url     : https://prove2.me/submissions/ce816a22-e849-42b6-9aa4-a0029206c81d

import Theorems.Thm_Freiman_lowerHistory_hazard_target

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (hw : lowerBoundedHistory h n) :
    lowerMixed (h n) → ¬ lowerH (h n) 2 → ¬ lowerH (h n) 5 → lowerLStar (h n) → lowerLocalLower (h n) ([2],[2]) ≤ lowerLocalCoordinate (h n) t := by
  intro hm h2 h5 hs
  have ht := lowerHistory_hazard_target t h n 3 hh (by simp) ⟨hm,h2,h5,hs⟩
  exact ht
