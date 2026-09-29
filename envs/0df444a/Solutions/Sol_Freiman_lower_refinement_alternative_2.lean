-- Prove2me | solution 2 for Freiman.lower_refinement_alternative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:14:20.067271+00:00
-- url     : https://prove2.me/submissions/9305ec51-fd63-444a-9fc8-8b0d500d7676

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_one_step
import Theorems.Thm_Freiman_lower_dependent_path

open Freiman

-- The dependent-path induction `lower_dependent_path` takes the single-step
-- progress statement as a hypothesis; `lower_one_step` is exactly that statement.
theorem solution (t : ℝ) (p : LowerPair) (hr : lowerInitialRoot t p) (hs : lowerState t p) :
    lowerHasValue t ∨ ∃ h : ℕ → LowerPair, lowerPath t h :=
  lower_dependent_path lower_one_step t p hr hs
