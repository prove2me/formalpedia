-- Prove2me | solution 1 for Freiman.lower_initial_seam_A
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:41.111302+00:00
-- url     : https://prove2.me/submissions/ea85d8bb-7af3-44ba-8088-9556a7a3bfe7

import Theorems.Thm_Freiman_lower_initial_contact
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution : ∀ n k, lowerContact (lowerNormalize (lowerFamilyPair .A n k 0)) [3,3,1,2,1,3] [3,1,2,1,3] [3,3,1,2,1,3] [2,1,3] := by
  intro n k
  by_cases hn : n=0
  · simpa only [lowerInitialSeamHolds, lowerInitialSeamWords, lowerInitialSeamFamily] using
      lower_initial_contact .aZero n k 0 (by simp [lowerInitialSeamZero,hn])
  · simpa only [lowerInitialSeamHolds, lowerInitialSeamWords, lowerInitialSeamFamily] using
      lower_initial_contact .aPos n k 0 (by simp [lowerInitialSeamZero,hn])

