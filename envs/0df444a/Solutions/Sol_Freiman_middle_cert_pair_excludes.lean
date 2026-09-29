-- Prove2me | solution 1 for Freiman.middle_cert_pair_excludes
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:24:20.064+00:00
-- url     : https://prove2.me/submissions/33fa80e1-d61a-442d-82ca-af580c669486

import Theorems.Thm_Freiman_middle_cert_pair_binding
import Theorems.Thm_Freiman_cert_witness_excludes
import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

theorem solution :
    ∀ (C : MiddleCertCatalog) (p : MiddleCertPair), middleCertWitnessesValid C → middleCertPairValid C p 0 → ∀ r s q : ℝ, certRectangleMem middleCertRectangle r s → ¬ (certBoundHolds (middleCertBound C p.lowerBound) r s q ∧ certBoundHolds (middleCertBound C p.upperBound) r s q) := by
  intro C p hw hp r s q hr
  exact cert_witness_excludes (middleCertPairWitness C p) (middle_cert_pair_binding C p hw hp) r s q hr
