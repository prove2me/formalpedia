-- Prove2me | solution 1 for Freiman.lower_marked_entry_transfer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:13.62187+00:00
-- url     : https://prove2.me/submissions/0141bd16-2480-435b-ad92-619fdceb8a0c

import Theorems.Thm_Freiman_lower_marked_entry_gluing
import Theorems.Thm_Freiman_lower_initial_bridge_A0
import Theorems.Thm_Freiman_lower_initial_bridge_An
import Theorems.Thm_Freiman_lower_initial_bridge_B
import Theorems.Thm_Freiman_lower_initial_bridge_C
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (hentry : ∀ (f : LowerInitialFamily) (n k p : ℕ), (∀ l ∈ lowerEntryLabels, lowerAdmissible (lowerChild (lowerFamilyPair f n k p) l) ∧ lowerGood (lowerChild (lowerFamilyPair f n k p) l) ∧ lowerParameterBox (lowerChild (lowerFamilyPair f n k p) l)) ∧ lowerFamilyH f n k p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild (lowerFamilyPair f n k p) l)})
    (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ) (ht : lowerInitialBaseSelected t f n k p) :
    ∃ r : LowerPair, lowerInitialRoot t r ∧ lowerState t r := by
  exact lower_marked_entry_gluing lower_initial_bridge_A0 lower_initial_bridge_An lower_initial_bridge_B lower_initial_bridge_C hentry t f n k p ht
