-- Prove2me | solution 1 for Freiman.middleRepair_equalIIbNormal_outer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:23.217816+00:00
-- url     : https://prove2.me/submissions/12b76065-6255-4f84-b16d-d4438f8674c7

import Theorems.Thm_Freiman_middleRepair_cert_interpret_outer
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbNormal → middleOuter c (middleRepairRowChildren c .equalIIbNormal) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 6 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨6,by decide⟩ hd
  exact middleRepair_cert_interpret_outer middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨6,by decide⟩ hd ha (by rfl)
