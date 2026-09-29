-- Prove2me | solution 1 for Freiman.middleRepair_equalIIa_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:23.029212+00:00
-- url     : https://prove2.me/submissions/347b4260-5b01-471f-ab88-66b05bfe15d1

import Theorems.Thm_Freiman_middleRepair_cert_interpret_goodness
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIa → ∀ d ∈ middleRepairRowChildren c .equalIIa, middleRepairGood d := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 5 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨5,by decide⟩ hd
  exact middleRepair_cert_interpret_goodness middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨5,by decide⟩ hd ha
