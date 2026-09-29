-- Prove2me | solution 1 for Freiman.lower_entry_family_context
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:12:09.617243+00:00
-- url     : https://prove2.me/submissions/0e31c69d-6dcc-4a47-aed7-c86773ba2404

import Theorems.Thm_Freiman_lower_entry_context_A
import Theorems.Thm_Freiman_lower_entry_context_B
import Theorems.Thm_Freiman_lower_entry_context_C
import Theorems.Thm_Freiman_lower_entry_context_auxB
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (f : LowerInitialFamily) (n k p : ℕ) : ∃ c : LowerEntryClass,
    lowerEntryContext c (lowerNormalize (lowerFamilyPair f n k p)) ∧
    lowerFamilyH f n k p = lowerEntryH c (lowerNormalize (lowerFamilyPair f n k p)) := by
  cases f
  · exact lower_entry_context_A n k p
  · exact lower_entry_context_B n k p
  · exact lower_entry_context_C n k p
  · exact lower_entry_context_auxB n k p
