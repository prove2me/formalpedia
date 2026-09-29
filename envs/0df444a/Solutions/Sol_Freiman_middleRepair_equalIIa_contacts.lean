-- Prove2me | solution 1 for Freiman.middleRepair_equalIIa_contacts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:22.862992+00:00
-- url     : https://prove2.me/submissions/2ee0b5bc-0de4-4370-9a2a-18bba22cf328

import Theorems.Thm_Freiman_middleRepair_cert_interpret_contacts
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIa → middleContacts (middleRepairRowChildren c .equalIIa) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 5 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨5,by decide⟩ hd
  exact middleRepair_cert_interpret_contacts middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨5,by decide⟩ hd ha
