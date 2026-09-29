-- Prove2me | solution 1 for Freiman.lower_entry_contact_rows
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:23.687548+00:00
-- url     : https://prove2.me/submissions/42254701-66fe-47a3-bcaa-88bb8a9c51c3

import Theorems.Thm_Freiman_lower_entry_row_application
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_lower_initial_matrix_bottom
import Theorems.Thm_Freiman_lower_entry_contact_parities
import Theorems.Thm_Freiman_lower_entry_contact_arithmetic_threeEven
import Theorems.Thm_Freiman_lower_entry_contact_arithmetic_threeOdd
import Theorems.Thm_Freiman_lower_entry_contact_arithmetic_twoOdd
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (c : LowerEntryClass) (p : LowerPair) (hc : lowerEntryContext c p)
    (hd : lowerEntryDomain p) : lowerEntryRowsHold p (lowerEntryContactRows c) := by
  intro e he
  apply lower_entry_row_application lower_initial_word_fraction lower_initial_matrix_bottom p e hd
    (lower_entry_contact_parities c p hc e he)
  cases c
  · exact lower_entry_contact_arithmetic_threeEven e he
  · exact lower_entry_contact_arithmetic_threeOdd e he
  · exact lower_entry_contact_arithmetic_twoOdd e he

