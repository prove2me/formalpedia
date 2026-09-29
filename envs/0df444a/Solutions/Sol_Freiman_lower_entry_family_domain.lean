-- Prove2me | solution 1 for Freiman.lower_entry_family_domain
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:10.527213+00:00
-- url     : https://prove2.me/submissions/c6e36b6b-a4c9-4f9a-8519-aebd96525afc

import Theorems.Thm_Freiman_lower_entry_seam_domain
import Theorems.Thm_Freiman_lower_entry_aux_domain
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (f : LowerInitialFamily) (n k p : ℕ) : lowerEntryDomain (lowerNormalize (lowerFamilyPair f n k p)) := by
  cases f with
  | A =>
    by_cases hn : n=0
    · exact lower_entry_seam_domain .aZero n k p (by simp [lowerInitialSeamZero,hn])
    · exact lower_entry_seam_domain .aPos n k p (by simp [lowerInitialSeamZero,hn])
  | B =>
    by_cases hn : n=0
    · exact lower_entry_seam_domain .b18Zero n k p (by simp [lowerInitialSeamZero,hn])
    · exact lower_entry_seam_domain .b18Pos n k p (by simp [lowerInitialSeamZero,hn])
  | C =>
    by_cases hn : n=0
    · exact lower_entry_seam_domain .cZero n k p (by simp [lowerInitialSeamZero,hn])
    · exact lower_entry_seam_domain .cPos n k p (by simp [lowerInitialSeamZero,hn])
  | auxB => exact lower_entry_aux_domain n k p
