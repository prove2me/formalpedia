-- Prove2me | solution 1 for Freiman.middleRepair_cert_record_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:38:19.463214+00:00
-- url     : https://prove2.me/submissions/a33c40fa-2956-4f1e-be5b-3da672284ee6

import Theorems.Thm_Freiman_middleRepair_cert_record_from_proof
import Theorems.Thm_Freiman_middle_cert_proof_sound
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect) (rec : MiddleCertRecord) (parent : ℤ), middleCertWitnessesValid C → middleRepairRecordValid C redirects rec parent → ∀ r s q : ℝ, certRectangleMem middleCertRectangle r s → ¬ middleCertHolds (middleRepairCertConditions C rec parent) r s q := by
  exact middleRepair_cert_record_from_proof middle_cert_proof_sound
