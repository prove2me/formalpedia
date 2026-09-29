-- Prove2me | solution 1 for Freiman.middleRepair_mixedB_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:52.821331+00:00
-- url     : https://prove2.me/submissions/72215062-3bd2-497d-8227-9011088035d2

import Theorems.Thm_Freiman_middleRepair_cert_interpret_goodness
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedB → ∀ d ∈ middleRepairRowChildren c .mixedB, middleRepairGood d := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 1 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨1,by decide⟩ hd
  exact middleRepair_cert_interpret_goodness middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨1,by decide⟩ hd ha
