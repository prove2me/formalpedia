-- Prove2me | solution 1 for Freiman.lower_initial_n_contact_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:59:04.856492+00:00
-- url     : https://prove2.me/submissions/47ce972c-edb3-400a-8a9d-88201c4b13de

import Theorems.Thm_Freiman_lower_initial_n_certificates
import Theorems.Thm_Freiman_cert_field_lower_bound
import Theorems.Thm_Freiman_lower_initial_n_base_n13
import Theorems.Thm_Freiman_lower_initial_n_base_n14
import Theorems.Thm_Freiman_lower_initial_n_base_aux
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialNCase) : lowerInitialNHolds c 0 := by
  have hv := lower_initial_n_certificates c
  have hp : 0 < certFieldVal (lowerInitialNBase c) :=
    lt_of_lt_of_le (by exact_mod_cast hv.2.2.2.2.2.2.2.2.2) (cert_field_lower_bound _)
  cases c
  · rw [lower_initial_n_base_n13] at hp
    simp only [lowerInitialNHolds, lowerRepeat, List.replicate_zero, List.flatten_nil, List.append_nil] 
    linarith
  · rw [lower_initial_n_base_n14] at hp
    simp only [lowerInitialNHolds, lowerRepeat, List.replicate_zero, List.flatten_nil, List.append_nil]
    linarith
  · rw [lower_initial_n_base_aux] at hp
    simp only [lowerInitialNHolds, lowerRepeat, List.replicate_zero, List.flatten_nil, List.append_nil]
    linarith
