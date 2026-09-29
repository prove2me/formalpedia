-- Prove2me | solution 1 for Freiman.lower_priority_choice
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:13.965223+00:00
-- url     : https://prove2.me/submissions/515f0654-4353-4548-bf2f-bbd4ad98d91b

import Theorems.Thm_Freiman_lower_priority_finite_selection
import Theorems.Thm_Freiman_lower_priority_blockers_good
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (trace : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t trace n)
    (h : ∃ l : LowerLabel, lowerOffered (trace n) l ∧ lowerGood (lowerChild (trace n) l) ∧ t ∈ lowerCover (lowerChild (trace n) l)) :
    ∃ l : LowerLabel, lowerOffered (trace n) l ∧ lowerPriority t (trace n) l ∧
      lowerGood (lowerChild (trace n) l) ∧ t ∈ lowerCover (lowerChild (trace n) l) := by
  exact lower_priority_finite_selection t (trace n) (lower_priority_blockers_good t trace n hh) h
