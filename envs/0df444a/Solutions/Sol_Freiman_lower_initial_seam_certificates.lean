-- Prove2me | solution 1 for Freiman.lower_initial_seam_certificates
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:17.315751+00:00
-- url     : https://prove2.me/submissions/4d14c1b4-3814-4672-9a58-719ca65d96d5

import Theorems.Thm_Freiman_lower_initial_seam_certificate_aZero
import Theorems.Thm_Freiman_lower_initial_seam_certificate_aPos
import Theorems.Thm_Freiman_lower_initial_seam_certificate_cZero
import Theorems.Thm_Freiman_lower_initial_seam_certificate_cPos
import Theorems.Thm_Freiman_lower_initial_seam_certificate_b18Zero
import Theorems.Thm_Freiman_lower_initial_seam_certificate_b18Pos
import Theorems.Thm_Freiman_lower_initial_seam_certificate_b19Zero
import Theorems.Thm_Freiman_lower_initial_seam_certificate_b19Pos
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution : ∀ c : LowerInitialSeamCase, lowerInitialSeamCertificateValid c := by
  intro c
  cases c
  · exact lower_initial_seam_certificate_aZero
  · exact lower_initial_seam_certificate_aPos
  · exact lower_initial_seam_certificate_cZero
  · exact lower_initial_seam_certificate_cPos
  · exact lower_initial_seam_certificate_b18Zero
  · exact lower_initial_seam_certificate_b18Pos
  · exact lower_initial_seam_certificate_b19Zero
  · exact lower_initial_seam_certificate_b19Pos
