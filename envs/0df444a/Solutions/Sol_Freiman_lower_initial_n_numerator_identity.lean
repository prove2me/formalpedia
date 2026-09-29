-- Prove2me | solution 1 for Freiman.lower_initial_n_numerator_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:53.055772+00:00
-- url     : https://prove2.me/submissions/9fa876d8-98d5-41c7-802d-285f548d520e

import Theorems.Thm_Freiman_lower_initial_n_numerator_n13
import Theorems.Thm_Freiman_lower_initial_n_numerator_n14
import Theorems.Thm_Freiman_lower_initial_n_numerator_aux
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialNCase) (x : ℝ) : lowerInitialNNumerator c x = lowerInitialNPolyEval c x := by
  cases c
  · exact lower_initial_n_numerator_n13 x
  · exact lower_initial_n_numerator_n14 x
  · exact lower_initial_n_numerator_aux x
