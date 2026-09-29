-- Prove2me | solution 2 for Freiman.lower_marked_entry_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:59:10.653358+00:00
-- url     : https://prove2.me/submissions/c10b78fb-89de-4af4-9d06-b4bb0b85af25

import Definitions.Def_Freiman_lowerBridgeCatalog
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_bridge_A0
import Theorems.Thm_Freiman_lower_initial_bridge_An
import Theorems.Thm_Freiman_lower_initial_bridge_B
import Theorems.Thm_Freiman_lower_initial_bridge_C
import Theorems.Thm_Freiman_lower_six_entry_geometry
import Theorems.Thm_Freiman_lower_marked_entry_gluing

open Freiman

-- `lower_marked_entry_gluing` (Proved) carries four bridge hypotheses plus the entry
-- geometry; the four bridge families are the three bridge nodes, and the entry geometry
-- is passed through from the target's own hypothesis.
theorem solution
    (hentry : ∀ (f : LowerInitialFamily) (n k p : ℕ),
      (∀ l ∈ lowerEntryLabels, lowerAdmissible (lowerChild (lowerFamilyPair f n k p) l) ∧
        lowerGood (lowerChild (lowerFamilyPair f n k p) l) ∧
        lowerParameterBox (lowerChild (lowerFamilyPair f n k p) l)) ∧
      lowerFamilyH f n k p ⊆
        {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild (lowerFamilyPair f n k p) l)})
    (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ) (ht : lowerInitialBaseSelected t f n k p) :
    ∃ r : LowerPair, lowerInitialRoot t r ∧ lowerState t r :=
  lower_marked_entry_gluing lower_initial_bridge_A0 lower_initial_bridge_An
    lower_initial_bridge_B lower_initial_bridge_C hentry t f n k p ht
