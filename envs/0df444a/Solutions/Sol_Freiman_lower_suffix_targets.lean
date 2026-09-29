-- Prove2me | solution 1 for Freiman.lower_suffix_targets
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:06.760314+00:00
-- url     : https://prove2.me/submissions/ff758187-1699-4981-863c-eb2b60c81d04

import Theorems.Thm_Freiman_lower_suffix_target_row1
import Theorems.Thm_Freiman_lower_suffix_target_row2
import Theorems.Thm_Freiman_lower_suffix_target_row3
import Theorems.Thm_Freiman_lower_suffix_target_row4
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    lowerSuffixBounds (h n) t := by
  exact ⟨lower_suffix_target_row1 t h n hh, lower_suffix_target_row2 t h n hh, lower_suffix_target_row3 t h n hh, lower_suffix_target_row4 t h n hh⟩
