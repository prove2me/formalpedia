-- Prove2me | solution 1 for Freiman.middleRepair_equalIIbShort_contacts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:38.802336+00:00
-- url     : https://prove2.me/submissions/960f8047-2dcb-40d1-a47b-904964955e5d

import Theorems.Thm_Freiman_middleRepair_cert_interpret_contacts
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbShort → middleContacts (middleRepairRowChildren c .equalIIbShort) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 7 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨7,by decide⟩ hd
  exact middleRepair_cert_interpret_contacts middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨7,by decide⟩ hd ha
