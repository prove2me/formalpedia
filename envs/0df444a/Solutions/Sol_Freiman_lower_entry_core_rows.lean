-- Prove2me | solution 1 for Freiman.lower_entry_core_rows
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:23.796891+00:00
-- url     : https://prove2.me/submissions/586834b6-4668-4f86-b4c2-12cc89f56f7e

import Theorems.Thm_Freiman_lower_entry_row_application
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_lower_initial_matrix_bottom
import Theorems.Thm_Freiman_lower_entry_core_parities
import Theorems.Thm_Freiman_lower_entry_core_arithmetic_threeEven
import Theorems.Thm_Freiman_lower_entry_core_arithmetic_threeOdd
import Theorems.Thm_Freiman_lower_entry_core_arithmetic_twoOdd
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (c : LowerEntryClass) (p : LowerPair) (hc : lowerEntryContext c p)
    (hd : lowerEntryDomain p) : lowerEntryRowsHold p (lowerEntryCoreRows c) := by
  intro e he
  apply lower_entry_row_application lower_initial_word_fraction lower_initial_matrix_bottom p e hd
    (lower_entry_core_parities c p hc e he)
  cases c
  · exact lower_entry_core_arithmetic_threeEven e he
  · exact lower_entry_core_arithmetic_threeOdd e he
  · exact lower_entry_core_arithmetic_twoOdd e he

