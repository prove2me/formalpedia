-- Prove2me | solution 1 for Freiman.middleRepair_cert_family_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:38:19.689192+00:00
-- url     : https://prove2.me/submissions/6373e2f2-4be9-4f3e-977e-dc7cc4ed2e4b

import Theorems.Thm_Freiman_middleRepair_cert_family_from_records
import Theorems.Thm_Freiman_middleRepair_cert_record_sound
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect) (f : ℕ), middleCertWitnessesValid C → middleCertFamilyValid C f → middleRepairBranchIdentity C → middleRepairLedgerValid C redirects → middleRepairCertFamilySound C f := by
  exact middleRepair_cert_family_from_records middleRepair_cert_record_sound
