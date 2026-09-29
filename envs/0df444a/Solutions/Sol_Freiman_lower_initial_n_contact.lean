-- Prove2me | solution 1 for Freiman.lower_initial_n_contact
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:59:05.560255+00:00
-- url     : https://prove2.me/submissions/347ea96e-5bb1-478d-b5fd-c135855c2aa0

import Theorems.Thm_Freiman_lower_initial_n_contact_zero
import Theorems.Thm_Freiman_lower_initial_n_contact_positive
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialNCase) (n : ℕ) : lowerInitialNHolds c n := by
  cases n with
  | zero => exact lower_initial_n_contact_zero c
  | succ n => exact lower_initial_n_contact_positive c (n+1) (Nat.zero_lt_succ n)
