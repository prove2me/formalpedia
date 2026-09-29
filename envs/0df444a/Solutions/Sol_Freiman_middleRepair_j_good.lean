-- Prove2me | solution 1 for Freiman.middleRepair_j_good
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:56.581242+00:00
-- url     : https://prove2.me/submissions/a914472a-03a3-4fe4-8f4d-335155f7f63a

import Theorems.Thm_Freiman_middle_j_real_ratio_bounds
import Theorems.Thm_Freiman_middleRepair_j_ratio_specialization
import Theorems.Thm_Freiman_middleRepair_j_regular_proper
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middleRepair_good38
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k → middleRepairGood (middleRepairJ c k) := by
  intro c r k hc hr hj hk
  have hd := middleRepair_j_regular_proper middleRepair_child_regular c k hc hk
  have hratio := middleRepair_j_ratio_specialization middle_j_real_ratio_bounds c r k hc hr hj hk
  exact middleRepair_good38 _ hd.1 hratio.2
