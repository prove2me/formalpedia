-- Prove2me | solution 1 for Freiman.middleRepair_cert_ledger_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:16.857187+00:00
-- url     : https://prove2.me/submissions/197d4b3f-1d0f-475c-aafd-1b3e60783e4e

import Theorems.Thm_Freiman_middleRepair_cert_redirect_keys
import Theorems.Thm_Freiman_middleRepair_cert_retained_pairs_valid
import Theorems.Thm_Freiman_middleRepair_cert_boundary_pairs_valid
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    middleRepairLedgerValid middleCertData middleRepairRedirects := by
  constructor
  · exact middleRepair_cert_redirect_keys
  · intro rec hr parent hp
    by_cases h : middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none
    · exact middleRepair_cert_retained_pairs_valid rec hr parent hp h
    · exact middleRepair_cert_boundary_pairs_valid rec hr parent hp h
