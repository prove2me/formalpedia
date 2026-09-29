-- Prove2me | solution 1 for Freiman.lower_suffix_target_row4
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:01.268978+00:00
-- url     : https://prove2.me/submissions/cee61c56-1200-4945-bdf2-56146fc7d215

import Theorems.Thm_Freiman_lower_history_certificate_row4
import Theorems.Thm_Freiman_lower_bounded_history
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    lowerMixed (h n) → ¬ lowerH (h n) 2 → ¬ lowerH (h n) 5 → ¬ lowerRStar (h n) := by
  exact lower_history_certificate_row4 t h n hh (lower_bounded_history t h n hh)
