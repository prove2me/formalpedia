-- Prove2me | solution 1 for Freiman.middleRepair_mixedA_contacts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:35.094479+00:00
-- url     : https://prove2.me/submissions/dceae6a8-7366-4705-b009-100ac85ff785

import Theorems.Thm_Freiman_middleRepair_cert_interpret_contacts
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedA → middleContacts (middleRepairRowChildren c .mixedA) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 0 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨0,by decide⟩ hd
  exact middleRepair_cert_interpret_contacts middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨0,by decide⟩ hd ha
