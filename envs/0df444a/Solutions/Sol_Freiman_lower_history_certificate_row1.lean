-- Prove2me | solution 1 for Freiman.lower_history_certificate_row1
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:28.098435+00:00
-- url     : https://prove2.me/submissions/75a22c04-f342-4b61-8de8-2400869e3997

import Theorems.Thm_Freiman_lowerHistory_hazard_target

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (hw : lowerBoundedHistory h n) :
    ¬ lowerMixed (h n) → ¬ lowerA (h n) 3 → ¬ lowerA (h n) 9 → lowerLStar (h n) → lowerLocalLower (h n) ([2],[1]) ≤ lowerLocalCoordinate (h n) t := by
  intro hm ha h9 hs
  have ht := lowerHistory_hazard_target t h n 1 hh (by simp) ⟨hm,ha,h9,hs⟩
  exact ht
