-- Prove2me | solution 1 for Freiman.lower_bounded_history
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:46.620067+00:00
-- url     : https://prove2.me/submissions/fe714142-d02c-4a14-a747-c81db3bf44bc

import Theorems.Thm_Freiman_lower_history_window_reduction
import Theorems.Thm_Freiman_lower_forced_reflections
import Theorems.Thm_Freiman_lower_generic_suffix_birth
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) : lowerBoundedHistory h n := by
  exact lower_history_window_reduction lower_forced_reflections lower_generic_suffix_birth t h n hh
