-- Prove2me | solution 2 for Freiman.lower_priority_choice
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T09:06:06.202269+00:00
-- url     : https://prove2.me/submissions/e470ea3c-3916-4757-978e-c3a0000a2389

import Definitions.Def_Freiman_lowerCertificates
import Theorems.Thm_Freiman_lower_priority_finite_selection
import Theorems.Thm_Freiman_lower_priority_blockers_good

open Freiman

theorem solution (t : ℝ) (trace : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t trace n)
    (h : ∃ l : LowerLabel, lowerOffered (trace n) l ∧
      lowerGood (lowerChild (trace n) l) ∧
      t ∈ lowerCover (lowerChild (trace n) l)) :
    ∃ l : LowerLabel, lowerOffered (trace n) l ∧
      lowerPriority t (trace n) l ∧
      lowerGood (lowerChild (trace n) l) ∧
      t ∈ lowerCover (lowerChild (trace n) l) := by
  exact lower_priority_finite_selection t (trace n)
    (lower_priority_blockers_good t trace n hh) h
