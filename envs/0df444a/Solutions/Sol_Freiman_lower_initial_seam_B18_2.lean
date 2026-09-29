-- Prove2me | solution 2 for Freiman.lower_initial_seam_B18
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:23:44.269547+00:00
-- url     : https://prove2.me/submissions/29dadd6d-33da-4d02-a23a-0aa61ab1307f

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_contact

open Freiman

open scoped BigOperators

-- The B18-seam quantifies over every `n`, so split on `n = 0` between the `.b18Zero`
-- and `.b18Pos` seam cases; both share family `.B` and the same words.
theorem solution : ∀ n k, lowerContact (lowerNormalize (lowerFamilyPair .B n k 0))
    [3,1,3,3,1,2,1,3] [3,1,2,1,3] [2,1,3,3,1,2,1,3] [2,1,3] := by
  intro n k
  by_cases h : n = 0
  · subst h
    simpa [lowerInitialSeamHolds, lowerInitialSeamFamily, lowerInitialSeamWords] using
      lower_initial_contact .b18Zero 0 k 0 (by decide)
  · simpa [lowerInitialSeamHolds, lowerInitialSeamFamily, lowerInitialSeamWords] using
      lower_initial_contact .b18Pos n k 0 (by simp [lowerInitialSeamZero, h])
