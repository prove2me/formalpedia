-- Prove2me | solution 1 for Freiman.lower_initial_seam_numerator_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:17.236566+00:00
-- url     : https://prove2.me/submissions/42caed0a-3b21-45a3-b917-499c48eb3567

import Theorems.Thm_Freiman_lower_initial_seam_numerator_aZero
import Theorems.Thm_Freiman_lower_initial_seam_numerator_aPos
import Theorems.Thm_Freiman_lower_initial_seam_numerator_cZero
import Theorems.Thm_Freiman_lower_initial_seam_numerator_cPos
import Theorems.Thm_Freiman_lower_initial_seam_numerator_b18Zero
import Theorems.Thm_Freiman_lower_initial_seam_numerator_b18Pos
import Theorems.Thm_Freiman_lower_initial_seam_numerator_b19Zero
import Theorems.Thm_Freiman_lower_initial_seam_numerator_b19Pos
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialSeamCase) (x y z : ℝ) : lowerInitialSeamNumerator c x y z = lowerInitialPolyEval (lowerInitialSeamPolynomial c) x y z := by
  cases c
  · exact lower_initial_seam_numerator_aZero x y z
  · exact lower_initial_seam_numerator_aPos x y z
  · exact lower_initial_seam_numerator_cZero x y z
  · exact lower_initial_seam_numerator_cPos x y z
  · exact lower_initial_seam_numerator_b18Zero x y z
  · exact lower_initial_seam_numerator_b18Pos x y z
  · exact lower_initial_seam_numerator_b19Zero x y z
  · exact lower_initial_seam_numerator_b19Pos x y z
