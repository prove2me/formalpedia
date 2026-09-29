-- Prove2me | solution 1 for Freiman.lower_initial_seam_aux
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:04:29.419229+00:00
-- url     : https://prove2.me/submissions/d3ca856e-e049-40be-87ba-74ef14157010

import Theorems.Thm_Freiman_lower_initial_n_contact
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution : ∀ n, lowerNContact n [3,1,3,1,2,1,3,1,2,3,1,2,1,3] [3,1,3,1,2,1,3,2,1,3] [3,1,3,1,2,1,3] [3,1,3,1,2,1,3] := by
  intro n
  simpa [lowerInitialNHolds, lowerInitialNWords, lowerNContact] using lower_initial_n_contact .aux n
