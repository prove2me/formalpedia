-- Prove2me | solution 1 for Freiman.lower_entry_seam_domain
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:10.368691+00:00
-- url     : https://prove2.me/submissions/12035869-9db7-4c88-a4cf-5572f70d84eb

import Theorems.Thm_Freiman_lower_entry_domain_transfer
import Theorems.Thm_Freiman_lower_initial_matrix_bottom
import Theorems.Thm_Freiman_lower_initial_family_matrix
import Theorems.Thm_Freiman_lower_entry_seam_matrix_domains
import Theorems.Thm_Freiman_lower_initial_parameter_box
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (c : LowerInitialSeamCase) (n k p : ℕ) (hc : lowerInitialSeamZero c = decide (n=0)) :
    lowerEntryDomain (lowerNormalize (lowerFamilyPair (lowerInitialSeamFamily c) n k p)) := by
  exact lower_entry_domain_transfer lower_initial_matrix_bottom _ _
    (lower_initial_family_matrix c n k p hc).2
    (lower_entry_seam_matrix_domains c _ _ _ (lower_initial_parameter_box n k p))
