-- Prove2me | solution 2 for Freiman.lower_initial_seam_A
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:23:39.559649+00:00
-- url     : https://prove2.me/submissions/3decdcf4-f790-4dbe-8889-99b12bf369f3

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_contact

open Freiman

open scoped BigOperators

-- The A-seam quantifies over every `n`, while the general seam identity splits the
-- `n = 0` side condition into two seam cases (`.aZero` for `n = 0`, `.aPos` otherwise).
-- Both share family `.A` and the same words, so each branch unfolds to this contact.
theorem solution : ∀ n k, lowerContact (lowerNormalize (lowerFamilyPair .A n k 0))
    [3,3,1,2,1,3] [3,1,2,1,3] [3,3,1,2,1,3] [2,1,3] := by
  intro n k
  by_cases h : n = 0
  · subst h
    simpa [lowerInitialSeamHolds, lowerInitialSeamFamily, lowerInitialSeamWords] using
      lower_initial_contact .aZero 0 k 0 (by decide)
  · simpa [lowerInitialSeamHolds, lowerInitialSeamFamily, lowerInitialSeamWords] using
      lower_initial_contact .aPos n k 0 (by simp [lowerInitialSeamZero, h])
