-- Prove2me | solution 1 for Freiman.lower_initial_seam_n14
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:04:28.823024+00:00
-- url     : https://prove2.me/submissions/53343ddd-dc32-421c-9dc0-22a0d1a22eff

import Theorems.Thm_Freiman_lower_initial_n_contact
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution : ∀ n, lowerNContact n [3,1,3,3,1,2,1,3] [3,3,1,2,1,3] [3,1,2,1,3] [3,1,2,1,3] := by
  intro n
  simpa [lowerInitialNHolds, lowerInitialNWords, lowerNContact] using lower_initial_n_contact .n14 n
