-- Prove2me | solution 1 for Freiman.lower_entry_aux_domain
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:10.530468+00:00
-- url     : https://prove2.me/submissions/77530435-ba4b-490c-b11b-4437172edaad

import Theorems.Thm_Freiman_lower_initial_period_ratio
import Theorems.Thm_Freiman_lower_entry_domain_transfer
import Theorems.Thm_Freiman_lower_initial_matrix_bottom
import Theorems.Thm_Freiman_lower_entry_aux_matrix
import Theorems.Thm_Freiman_lower_initial_period_matrix
import Theorems.Thm_Freiman_lower_initial_period_positive
import Theorems.Thm_Freiman_lower_entry_domain_matrix_aux
import Theorems.Thm_Freiman_lower_entry_domain_normalizes
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (n k p : ℕ) : lowerEntryDomain (lowerNormalize (lowerFamilyPair .auxB n k p)) := by
  have hx := lower_initial_period_ratio (n+1)
  have hd := lower_entry_domain_transfer lower_initial_matrix_bottom _ _
    (lower_entry_aux_matrix lower_initial_period_matrix lower_initial_period_positive n k p)
    (lower_entry_domain_matrix_aux _ ⟨hx.1,hx.2.2⟩)
  have hn := lower_entry_domain_normalizes lower_initial_word_fraction lower_initial_matrix_bottom _ hd
  simpa only [hn] using hd
