-- Prove2me | solution 1 for Freiman.middleRepair_mixedB_outer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:52.812609+00:00
-- url     : https://prove2.me/submissions/23117d42-e1cb-4b31-9c32-1c684ae38498

import Theorems.Thm_Freiman_middleRepair_cert_interpret_outer
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedB → middleOuter c (middleRepairRowChildren c .mixedB) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 1 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨1,by decide⟩ hd
  exact middleRepair_cert_interpret_outer middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨1,by decide⟩ hd ha (by rfl)
