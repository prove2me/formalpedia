-- Prove2me | solution 1 for Freiman.lower_history_certificate_row4
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:41.132988+00:00
-- url     : https://prove2.me/submissions/107c0a62-9c2e-43b4-ba4a-e73901c813cb

import Theorems.Thm_Freiman_lowerHistory_hazard_target

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (hw : lowerBoundedHistory h n) :
    lowerMixed (h n) → ¬ lowerH (h n) 2 → ¬ lowerH (h n) 5 → ¬ lowerRStar (h n) := by
  intro hm h2 h5 hs
  have ht := lowerHistory_hazard_target t h n 4 hh (by simp) ⟨hm,h2,h5,hs⟩
  exact ht
