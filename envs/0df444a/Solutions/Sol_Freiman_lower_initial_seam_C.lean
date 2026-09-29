-- Prove2me | solution 1 for Freiman.lower_initial_seam_C
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:41.151495+00:00
-- url     : https://prove2.me/submissions/d357cf60-01df-42d7-b5e3-b6a04fa3ff77

import Theorems.Thm_Freiman_lower_initial_contact
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution : ∀ n k p, lowerContact (lowerNormalize (lowerFamilyPair .C n k p)) [3,3,1,2,1,3] [3,1,2,1,3] [3,3,1,2,1,3] [2,1,3] := by
  intro n k p
  by_cases hn : n=0
  · simpa only [lowerInitialSeamHolds, lowerInitialSeamWords, lowerInitialSeamFamily] using
      lower_initial_contact .cZero n k p (by simp [lowerInitialSeamZero,hn])
  · simpa only [lowerInitialSeamHolds, lowerInitialSeamWords, lowerInitialSeamFamily] using
      lower_initial_contact .cPos n k p (by simp [lowerInitialSeamZero,hn])

