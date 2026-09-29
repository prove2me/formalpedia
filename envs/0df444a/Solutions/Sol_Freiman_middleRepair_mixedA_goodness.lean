-- Prove2me | solution 1 for Freiman.middleRepair_mixedA_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:35.511259+00:00
-- url     : https://prove2.me/submissions/2161af0f-b503-42fa-8209-aee5d9711e62

import Theorems.Thm_Freiman_middleRepair_cert_interpret_goodness
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedA → ∀ d ∈ middleRepairRowChildren c .mixedA, middleRepairGood d := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 0 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨0,by decide⟩ hd
  exact middleRepair_cert_interpret_goodness middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨0,by decide⟩ hd ha
