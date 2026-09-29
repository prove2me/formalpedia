-- Prove2me | solution 1 for Freiman.middleRepair_mixed31_good
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:57.387883+00:00
-- url     : https://prove2.me/submissions/96a01a4f-a3b7-4578-a1b9-4520049b45b3

import Theorems.Thm_Freiman_middle_mixed31_real_bounds
import Theorems.Thm_Freiman_middleRepair_mixed31_width_from_real_bounds
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middleRepair_good38
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRowCondition c .mixedC → middleRepairGood (middleRepairChild c [3] [1]) := by
  intro c hc hr
  have hd := middleRepair_child_regular c [3] [1] hc (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
  exact middleRepair_good38 _ hd.1 (middleRepair_mixed31_width_from_real_bounds middle_mixed31_real_bounds c hc hr)
