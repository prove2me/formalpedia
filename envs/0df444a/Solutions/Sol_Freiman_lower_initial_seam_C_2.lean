-- Prove2me | solution 2 for Freiman.lower_initial_seam_C
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:17:27.643833+00:00
-- url     : https://prove2.me/submissions/e84ea754-8f41-43b1-9f2d-c1909b997a5e

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_contact

open Freiman

open scoped BigOperators

-- The C-seam covers every `n`, so split on `n = 0`: the zero branch is the `.cZero`
-- seam identity and the positive branch is `.cPos`. Both unfold to this same contact.
theorem solution : ∀ n k p, lowerContact (lowerNormalize (lowerFamilyPair .C n k p))
    [3,3,1,2,1,3] [3,1,2,1,3] [3,3,1,2,1,3] [2,1,3] := by
  intro n k p
  by_cases h : n = 0
  · subst h
    simpa [lowerInitialSeamHolds, lowerInitialSeamFamily, lowerInitialSeamWords] using
      lower_initial_contact .cZero 0 k p (by decide)
  · simpa [lowerInitialSeamHolds, lowerInitialSeamFamily, lowerInitialSeamWords] using
      lower_initial_contact .cPos n k p (by simp [lowerInitialSeamZero, h])
