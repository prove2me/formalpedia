-- Prove2me | solution 1 for Freiman.middleRepair_cert_catalog_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:17.144256+00:00
-- url     : https://prove2.me/submissions/79b106fd-5eeb-418d-88e5-7cba75910db2

import Theorems.Thm_Freiman_middleRepair_cert_family_sound
import Theorems.Thm_Freiman_middle_cert_all_witnesses_valid
import Theorems.Thm_Freiman_middle_cert_all_families_valid
import Theorems.Thm_Freiman_middleRepair_cert_branch_identity
import Theorems.Thm_Freiman_middleRepair_cert_ledger_valid
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ f : Fin 11, middleRepairCertFamilySound middleCertData f.val := by
  intro f
  exact middleRepair_cert_family_sound middleCertData middleRepairRedirects f.val middle_cert_all_witnesses_valid (middle_cert_all_families_valid f) middleRepair_cert_branch_identity middleRepair_cert_ledger_valid
