-- Prove2me | solution 1 for Freiman.middleRepair_equalIJ_contacts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:07.776583+00:00
-- url     : https://prove2.me/submissions/205de642-c064-41e6-9539-36bc72a4bb8f

import Theorems.Thm_Freiman_middleRepair_cert_interpret_contacts
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIJ → middleContacts (middleRepairRowChildren c .equalIJ) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 4 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨4,by decide⟩ hd
  exact middleRepair_cert_interpret_contacts middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨4,by decide⟩ hd ha
