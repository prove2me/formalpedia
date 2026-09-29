-- Prove2me | solution 1 for Freiman.lower_initial_seam_B19
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:53.175785+00:00
-- url     : https://prove2.me/submissions/797934c0-bc6d-46b0-b7e9-0026a15b66ae

import Theorems.Thm_Freiman_lower_initial_contact
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution : ∀ n k, lowerContact (lowerNormalize (lowerFamilyPair .B n k 0)) [3,3,1,2,1,3] [3,1,3,1,2,1,3] [3,3,1,2,1,3] [2,1,3,1,2,1,3] := by
  intro n k
  by_cases hn : n=0
  · simpa only [lowerInitialSeamHolds, lowerInitialSeamWords, lowerInitialSeamFamily] using
      lower_initial_contact .b19Zero n k 0 (by simp [lowerInitialSeamZero,hn])
  · simpa only [lowerInitialSeamHolds, lowerInitialSeamWords, lowerInitialSeamFamily] using
      lower_initial_contact .b19Pos n k 0 (by simp [lowerInitialSeamZero,hn])

