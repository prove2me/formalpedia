-- Prove2me | solution 1 for Freiman.middleRepair_equalIShort_contacts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:07.738683+00:00
-- url     : https://prove2.me/submissions/0855120c-742c-4d1c-a5d2-f008e485bb7a

import Theorems.Thm_Freiman_middleRepair_cert_interpret_contacts
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIShort → middleContacts (middleRepairRowChildren c .equalIShort) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 3 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨3,by decide⟩ hd
  exact middleRepair_cert_interpret_contacts middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨3,by decide⟩ hd ha
