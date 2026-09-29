-- Prove2me | solution 1 for Freiman.middleRepair_equalIIbJ_contacts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:38.923436+00:00
-- url     : https://prove2.me/submissions/2b93330b-8a67-44f5-8a8b-663a18036f39

import Theorems.Thm_Freiman_middleRepair_cert_interpret_contacts
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbJ → middleContacts (middleRepairRowChildren c .equalIIbJ) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 8 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨8,by decide⟩ hd
  exact middleRepair_cert_interpret_contacts middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨8,by decide⟩ hd ha
