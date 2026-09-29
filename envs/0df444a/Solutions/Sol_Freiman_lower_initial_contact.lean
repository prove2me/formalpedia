-- Prove2me | solution 1 for Freiman.lower_initial_contact
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:41.366974+00:00
-- url     : https://prove2.me/submissions/a098e4c5-d988-420b-b76c-8917e75b8fcc

import Theorems.Thm_Freiman_lower_initial_parameter_box
import Theorems.Thm_Freiman_lower_initial_contact_transfer
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_lower_initial_family_matrix
import Theorems.Thm_Freiman_lower_initial_seam_denominators
import Theorems.Thm_Freiman_lower_initial_seam_numerator_positive
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialSeamCase) (n k p : ℕ)
    (hc : lowerInitialSeamZero c = decide (n=0)) : lowerInitialSeamHolds c n k p := by
  have hb := lower_initial_parameter_box n k p
  exact lower_initial_contact_transfer lower_initial_word_fraction c n k p
    (lower_initial_family_matrix c n k p hc)
    (lower_initial_seam_denominators c _ _ _ hb)
    (lower_initial_seam_numerator_positive c _ _ _ hb)
