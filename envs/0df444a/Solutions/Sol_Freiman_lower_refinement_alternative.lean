-- Prove2me | solution 1 for Freiman.lower_refinement_alternative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:20.637667+00:00
-- url     : https://prove2.me/submissions/698a2330-ec14-4b63-902b-17b8ea46793a

import Theorems.Thm_Freiman_lower_dependent_path
import Theorems.Thm_Freiman_lower_one_step
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hr : lowerInitialRoot t p) (hs : lowerState t p) :
    lowerHasValue t ∨ ∃ h : ℕ → LowerPair, lowerPath t h := by
  exact lower_dependent_path lower_one_step t p hr hs
