-- Prove2me | solution 1 for Freiman.middleRepair_mixedC_outer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:52.589979+00:00
-- url     : https://prove2.me/submissions/4088c152-fce1-41b3-8407-1e6cd1b9152d

import Theorems.Thm_Freiman_middleRepair_cert_interpret_outer
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedC → middleOuter c (middleRepairRowChildren c .mixedC) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 2 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨2,by decide⟩ hd
  exact middleRepair_cert_interpret_outer middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨2,by decide⟩ hd ha (by rfl)
