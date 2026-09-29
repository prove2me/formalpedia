-- Prove2me | solution 1 for Freiman.lower_initial_seam_numerator_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:29.424425+00:00
-- url     : https://prove2.me/submissions/84e151bb-4b1d-4421-8582-e4b2431846dc

import Theorems.Thm_Freiman_lower_initial_seam_numerator_identity
import Theorems.Thm_Freiman_lower_initial_tensor_positive
import Theorems.Thm_Freiman_lower_initial_seam_certificates
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialSeamCase) (x y z : ℝ) (hb : lowerInitialBox x y z) : 0 < lowerInitialSeamNumerator c x y z := by
  rw [lower_initial_seam_numerator_identity]
  exact lower_initial_tensor_positive c (lower_initial_seam_certificates c) x y z hb
