-- Prove2me | solution 1 for Freiman.lower_entry_child_parameter
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:35.867637+00:00
-- url     : https://prove2.me/submissions/8ee3b17b-76b0-45ae-b93a-aab4675aa0d7

import Theorems.Thm_Freiman_lower_parameter_extension
import Theorems.Thm_Freiman_lower_entry_child_extends
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (p : LowerPair) (hd : lowerEntryDomain p) (hn : lowerNormalize p = p) : ∀ l ∈ lowerEntryLabels, lowerParameterBox (lowerChild p l) := by
  intro l hl
  rcases hd with ⟨_,_,hr0,hr1,hs0,hs1⟩
  apply lower_parameter_extension p _
  · exact ⟨le_of_lt hr0,by linarith,le_of_lt hs0,by linarith⟩
  · exact lower_entry_child_extends p hn l hl
