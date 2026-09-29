-- Prove2me | solution 1 for Freiman.middleRepair_mixedC_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:56.358188+00:00
-- url     : https://prove2.me/submissions/9d3229a6-3c34-42a1-9d95-77a0395097e3

import Theorems.Thm_Freiman_middleRepair_mixedC_other_goodness
import Theorems.Thm_Freiman_middleRepair_mixed31_good
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedC → ∀ d ∈ middleRepairRowChildren c .mixedC, middleRepairGood d := by
  intro c hc hg hr d hd
  have hother := middleRepair_mixedC_other_goodness c hc hg hr
  simp only [middleRepairRowChildren, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact middleRepair_mixed31_good c hc hr
  · exact hother.1
  · exact hother.2
