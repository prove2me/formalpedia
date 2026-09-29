-- Prove2me | solution 1 for Freiman.middleRepair_mixedC_other_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:57.235221+00:00
-- url     : https://prove2.me/submissions/9d0e7822-a9a4-4ff3-a65a-12825d97c1d1

import Theorems.Thm_Freiman_middleRepair_cert_interpret_goodness
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedC →
      middleRepairGood (middleRepairChild c [2] []) ∧ middleRepairGood (middleRepairChild c [1] []) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 2 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨2,by decide⟩ hd
  have hgood := middleRepair_cert_interpret_goodness middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨2,by decide⟩ hd ha
  constructor
  · exact hgood (middleRepairChild c [2] []) (by simp [middleRepairRowChildren, middleCertRow])
  · exact hgood (middleRepairChild c [1] []) (by simp [middleRepairRowChildren, middleCertRow])
