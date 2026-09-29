-- Prove2me | solution 1 for Freiman.middle_cert_proof_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:18.649846+00:00
-- url     : https://prove2.me/submissions/6b8bed02-60b1-4d80-beb0-2b31a847fd24

import Theorems.Thm_Freiman_middle_cert_proof_from_pair_diagonal
import Theorems.Thm_Freiman_middle_cert_pair_excludes
import Theorems.Thm_Freiman_cert_diagonal_threshold_order
import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

theorem solution :
    ∀ (C : MiddleCertCatalog) (p : MiddleCertProof), middleCertWitnessesValid C → middleCertProofValid C p → middleCertProofSound C p := by
  exact middle_cert_proof_from_pair_diagonal middle_cert_pair_excludes cert_diagonal_threshold_order
