-- Prove2me | solution 1 for Freiman.middleRepair_good38
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:35.398868+00:00
-- url     : https://prove2.me/submissions/bdafb224-5179-486b-9948-a0fd81debd9e

import Theorems.Thm_Freiman_middleRepair_cert_interpret_uniform
import Theorems.Thm_Freiman_middleRepair_cert_uniform_family
import Theorems.Thm_Freiman_middleRepair_cert_actual_family
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middle_endpoint_order
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRatio c < (19/5:ℝ) → middleRepairGood c := by
  intro c hr hratio
  obtain ⟨f,hf,hd⟩ := middleRepair_cert_uniform_family c hr hratio
  exact middleRepair_cert_interpret_uniform middleRepair_goodness_criterion middleRepair_child_regular middle_endpoint_order c hr ⟨f,hf,hd,middleRepair_cert_actual_family c f hd⟩
