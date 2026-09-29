-- Prove2me | solution 1 for Freiman.lower_initial_n_contact_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:59:05.150825+00:00
-- url     : https://prove2.me/submissions/06bb41f9-3ef2-40f1-85ae-4ac2d939fac9

import Theorems.Thm_Freiman_lower_initial_period_ratio
import Theorems.Thm_Freiman_lower_initial_n_contact_transfer
import Theorems.Thm_Freiman_lower_initial_period_matrix
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_lower_initial_period_positive
import Theorems.Thm_Freiman_lower_initial_n_denominators
import Theorems.Thm_Freiman_lower_initial_n_positive
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialNCase) (n : ℕ) (hn : 0 < n) : lowerInitialNHolds c n := by
  have hx := lower_initial_period_ratio n
  exact lower_initial_n_contact_transfer lower_initial_period_matrix lower_initial_word_fraction c n hn
    (lower_initial_period_positive n hn)
    (lower_initial_n_denominators c _ ⟨hx.1,hx.2.2⟩) (lower_initial_n_positive c n)
