-- Prove2me | solution 1 for Freiman.lower_initial_seam_B18
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:41.336081+00:00
-- url     : https://prove2.me/submissions/560a0fed-eb3f-422e-b9e0-487d49dc17a4

import Theorems.Thm_Freiman_lower_initial_contact
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution : ∀ n k, lowerContact (lowerNormalize (lowerFamilyPair .B n k 0)) [3,1,3,3,1,2,1,3] [3,1,2,1,3] [2,1,3,3,1,2,1,3] [2,1,3] := by
  intro n k
  by_cases hn : n=0
  · simpa only [lowerInitialSeamHolds, lowerInitialSeamWords, lowerInitialSeamFamily] using
      lower_initial_contact .b18Zero n k 0 (by simp [lowerInitialSeamZero,hn])
  · simpa only [lowerInitialSeamHolds, lowerInitialSeamWords, lowerInitialSeamFamily] using
      lower_initial_contact .b18Pos n k 0 (by simp [lowerInitialSeamZero,hn])

