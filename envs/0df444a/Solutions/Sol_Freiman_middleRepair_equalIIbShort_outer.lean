-- Prove2me | solution 1 for Freiman.middleRepair_equalIIbShort_outer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:38.99778+00:00
-- url     : https://prove2.me/submissions/5146cf43-c374-406d-af4c-22c7ccddd01f

import Theorems.Thm_Freiman_middleRepair_cert_interpret_outer
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbShort → middleOuter c (middleRepairRowChildren c .equalIIbShort) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 7 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨7,by decide⟩ hd
  exact middleRepair_cert_interpret_outer middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨7,by decide⟩ hd ha (by rfl)
