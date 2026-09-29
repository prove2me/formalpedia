-- Prove2me | solution 1 for Freiman.lower_entry_admissible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:24.441984+00:00
-- url     : https://prove2.me/submissions/64d25302-de24-425f-8b27-4a854a0232f5

import Theorems.Thm_Freiman_lower_entry_admissible_A
import Theorems.Thm_Freiman_lower_entry_admissible_B
import Theorems.Thm_Freiman_lower_entry_admissible_C
import Theorems.Thm_Freiman_lower_entry_admissible_auxB
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (f : LowerInitialFamily) (n k p : ℕ) : ∀ l ∈ lowerEntryLabels, lowerAdmissible (lowerChild (lowerFamilyPair f n k p) l) := by
  cases f
  · exact lower_entry_admissible_A n k p
  · exact lower_entry_admissible_B n k p
  · exact lower_entry_admissible_C n k p
  · exact lower_entry_admissible_auxB n k p
