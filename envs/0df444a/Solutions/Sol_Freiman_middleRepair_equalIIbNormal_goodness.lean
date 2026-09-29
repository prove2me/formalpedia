-- Prove2me | solution 1 for Freiman.middleRepair_equalIIbNormal_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:22.943989+00:00
-- url     : https://prove2.me/submissions/8894fe19-0252-4673-ba6b-e780acaa0660

import Theorems.Thm_Freiman_middleRepair_cert_interpret_goodness
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbNormal → ∀ d ∈ middleRepairRowChildren c .equalIIbNormal, middleRepairGood d := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 6 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨6,by decide⟩ hd
  exact middleRepair_cert_interpret_goodness middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨6,by decide⟩ hd ha
