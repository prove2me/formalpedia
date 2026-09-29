-- Prove2me | solution 1 for Freiman.lower_entry_seam_matrix_domains
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:04:43.285646+00:00
-- url     : https://prove2.me/submissions/b373d1bd-21a1-4782-ad3d-da24969634cf

import Theorems.Thm_Freiman_lower_entry_domain_matrix_aZero
import Theorems.Thm_Freiman_lower_entry_domain_matrix_aPos
import Theorems.Thm_Freiman_lower_entry_domain_matrix_b18Zero
import Theorems.Thm_Freiman_lower_entry_domain_matrix_b18Pos
import Theorems.Thm_Freiman_lower_entry_domain_matrix_cZero
import Theorems.Thm_Freiman_lower_entry_domain_matrix_cPos
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (c : LowerInitialSeamCase) (x y z : ℝ) (hb : lowerInitialBox x y z) : lowerEntryMatrixBounds (lowerInitialSeamMatrices c x y z) := by
  cases c
  · exact lower_entry_domain_matrix_aZero x y z hb
  · exact lower_entry_domain_matrix_aPos x y z hb
  · exact lower_entry_domain_matrix_cZero x y z hb
  · exact lower_entry_domain_matrix_cPos x y z hb
  · exact lower_entry_domain_matrix_b18Zero x y z hb
  · exact lower_entry_domain_matrix_b18Pos x y z hb
  · exact lower_entry_domain_matrix_b18Zero x y z hb
  · exact lower_entry_domain_matrix_b18Pos x y z hb
