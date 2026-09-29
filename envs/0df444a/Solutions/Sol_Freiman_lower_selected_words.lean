-- Prove2me | solution 1 for Freiman.lower_selected_words
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:22.548855+00:00
-- url     : https://prove2.me/submissions/0b7f483c-539a-4797-82e4-c970e48094cf

import Theorems.Thm_Freiman_lower_guard_selected_extension
import Theorems.Thm_Freiman_lower_guard_admissible_extension
import Definitions.Def_Freiman_lowerWordGuardData

open Freiman
theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (l : LowerLabel) (hl : lowerOffered (h n) l) :
    lowerAdmissible (lowerChild (h n) l) ∧ lowerExtends (lowerNormalize (h n)) (lowerChild (h n) l) ∧
      lowerPrefixSize (h n) < lowerPrefixSize (lowerChild (h n) l) := by
  have hp := (hh.2.1 n (Nat.le_refl n)).1
  have he := lower_guard_selected_extension (h n) hp l hl
  exact ⟨lower_guard_admissible_extension (h n) hp l he,he.1,he.2.1⟩
