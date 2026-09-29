-- Prove2me | solution 2 for Freiman.lower_initial_seams
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:29:22.832579+00:00
-- url     : https://prove2.me/submissions/0b3ca77d-1336-415b-8d2d-946314bade88

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_seam_A
import Theorems.Thm_Freiman_lower_initial_seam_C
import Theorems.Thm_Freiman_lower_initial_seam_B18
import Theorems.Thm_Freiman_lower_initial_seam_B19
import Theorems.Thm_Freiman_lower_initial_seam_n13
import Theorems.Thm_Freiman_lower_initial_seam_n14
import Theorems.Thm_Freiman_lower_initial_seam_aux

open Freiman

open scoped BigOperators

-- `lowerInitialSeams` is a seven-fold conjunction, and the seven conjuncts are exactly
-- the four seam-contact statements plus the three `lowerNContact` statements.
theorem solution : lowerInitialSeams := by
  unfold lowerInitialSeams
  exact ⟨lower_initial_seam_A, lower_initial_seam_C, lower_initial_seam_B18,
    lower_initial_seam_B19, lower_initial_seam_n13, lower_initial_seam_n14,
    lower_initial_seam_aux⟩
