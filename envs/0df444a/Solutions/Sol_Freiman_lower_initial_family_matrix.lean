-- Prove2me | solution 1 for Freiman.lower_initial_family_matrix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:29.431022+00:00
-- url     : https://prove2.me/submissions/b673c164-8a31-4f8c-bdfc-b52397e3a0f1

import Theorems.Thm_Freiman_lower_initial_family_matrix_transfer
import Theorems.Thm_Freiman_lower_initial_period_matrix
import Theorems.Thm_Freiman_lower_initial_period_positive
import Theorems.Thm_Freiman_lower_initial_run_positive
import Theorems.Thm_Freiman_lower_initial_run_matrix
import Theorems.Thm_Freiman_lower_initial_family_normalization
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialSeamCase) (n k p : ℕ) (hc : lowerInitialSeamZero c = decide (n=0)) : lowerInitialSeamLink c n k p := by
  exact lower_initial_family_matrix_transfer lower_initial_period_matrix lower_initial_period_positive lower_initial_run_positive lower_initial_run_matrix lower_initial_family_normalization c n k p hc
