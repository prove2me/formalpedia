-- Prove2me | solution 2 for Freiman.lower_initial_seam_B19
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:23:49.588547+00:00
-- url     : https://prove2.me/submissions/0ed35a21-0ddd-488e-9923-196943ddd99c

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_contact

open Freiman

open scoped BigOperators

-- The B19-seam quantifies over every `n`, so split on `n = 0` between the `.b19Zero`
-- and `.b19Pos` seam cases; both share family `.B` and the same words.
theorem solution : ∀ n k, lowerContact (lowerNormalize (lowerFamilyPair .B n k 0))
    [3,3,1,2,1,3] [3,1,3,1,2,1,3] [3,3,1,2,1,3] [2,1,3,1,2,1,3] := by
  intro n k
  by_cases h : n = 0
  · subst h
    simpa [lowerInitialSeamHolds, lowerInitialSeamFamily, lowerInitialSeamWords] using
      lower_initial_contact .b19Zero 0 k 0 (by decide)
  · simpa [lowerInitialSeamHolds, lowerInitialSeamFamily, lowerInitialSeamWords] using
      lower_initial_contact .b19Pos n k 0 (by simp [lowerInitialSeamZero, h])
