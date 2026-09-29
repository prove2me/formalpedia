-- Prove2me | solution 1 for Freiman.lower_suffix_target_row2
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:00.778975+00:00
-- url     : https://prove2.me/submissions/acbb1ce7-8acd-493a-91d9-916b18778c32

import Theorems.Thm_Freiman_lower_history_certificate_row2
import Theorems.Thm_Freiman_lower_bounded_history
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    ¬ lowerMixed (h n) → ¬ lowerA (h n) 3 → lowerRStar (h n) → lowerLocalLower (h n) ([2],[2]) ≤ lowerLocalCoordinate (h n) t := by
  exact lower_history_certificate_row2 t h n hh (lower_bounded_history t h n hh)
