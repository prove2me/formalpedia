-- Prove2me | solution 2 for Freiman.lower_initial_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:14:45.417385+00:00
-- url     : https://prove2.me/submissions/d3f050c0-591a-4050-aed2-15bd71d906bf

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_lower_initial_parameter_box
import Theorems.Thm_Freiman_lower_initial_seam_denominators
import Theorems.Thm_Freiman_lower_initial_seam_numerator_positive
import Theorems.Thm_Freiman_lower_initial_family_matrix
import Theorems.Thm_Freiman_lower_initial_contact_transfer

open Freiman

open scoped BigOperators

-- `lower_initial_contact_transfer` needs four inputs, and each is an existing node:
-- the word/matrix identity is exactly `lower_initial_word_fraction`; the seam link is
-- `lower_initial_family_matrix`; and the denominator/numerator positivity facts follow
-- from `lower_initial_parameter_box` by the two Proved seam lemmas.
theorem solution (c : LowerInitialSeamCase) (n k p : ℕ)
    (hc : lowerInitialSeamZero c = decide (n = 0)) : lowerInitialSeamHolds c n k p :=
  lower_initial_contact_transfer
    (fun w t ht => lower_initial_word_fraction w t ht)
    c n k p
    (lower_initial_family_matrix c n k p hc)
    (lower_initial_seam_denominators c (lowerInitialX n) (lowerInitialY k) (lowerInitialY p)
      (lower_initial_parameter_box n k p))
    (lower_initial_seam_numerator_positive c (lowerInitialX n) (lowerInitialY k) (lowerInitialY p)
      (lower_initial_parameter_box n k p))
