-- Prove2me | solution 1 for Freiman.middleRepair_equalIJ_anchors
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:07.908254+00:00
-- url     : https://prove2.me/submissions/5bc66b9b-c0a5-414d-a42f-e7346c6a501a

import Theorems.Thm_Freiman_middleRepair_cert_interpret_J_anchors
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIJ → middleRepairJAnchors c (middleRepairRowChildren c .equalIJ) := by
  intro c hr hg hc
  have hd : middleRepairCertDomain c 4 := ⟨hr,hg,hc⟩
  have ha := middleRepair_cert_actual_family c ⟨4,by decide⟩ hd
  exact middleRepair_cert_interpret_J_anchors middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c ⟨4,by decide⟩ hd ha (by rfl)
