-- Prove2me | solution 1 for Freiman.lower_suffix_target_row3
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:01.01301+00:00
-- url     : https://prove2.me/submissions/da515232-7e01-40e4-aa65-5933bc2d9ce2

import Theorems.Thm_Freiman_lower_history_certificate_row3
import Theorems.Thm_Freiman_lower_bounded_history
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    lowerMixed (h n) → ¬ lowerH (h n) 2 → ¬ lowerH (h n) 5 → lowerLStar (h n) → lowerLocalLower (h n) ([2],[2]) ≤ lowerLocalCoordinate (h n) t := by
  exact lower_history_certificate_row3 t h n hh (lower_bounded_history t h n hh)
