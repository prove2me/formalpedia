-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0500_0550
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T23:52:59.237644+00:00
-- url     : https://prove2.me/submissions/15f6569f-15eb-4af1-8f26-e1577f3b3694

import Theorems.Thm_Freiman_lowerHistory_bindings_0500_0505
import Theorems.Thm_Freiman_lowerHistory_bindings_0505_0510
import Theorems.Thm_Freiman_lowerHistory_bindings_0510_0515
import Theorems.Thm_Freiman_lowerHistory_bindings_0515_0520
import Theorems.Thm_Freiman_lowerHistory_bindings_0520_0525
import Theorems.Thm_Freiman_lowerHistory_bindings_0525_0530
import Theorems.Thm_Freiman_lowerHistory_bindings_0530_0535
import Theorems.Thm_Freiman_lowerHistory_bindings_0535_0540
import Theorems.Thm_Freiman_lowerHistory_bindings_0540_0545
import Theorems.Thm_Freiman_lowerHistory_bindings_0545_0550
open Freiman
theorem solution : lowerHistoryBindingBatch 500 550 := by
  intro i hlo hhi p hp
  by_cases h500 : i < 505
  · exact Freiman.lowerHistory_bindings_0500_0505 i (by omega) h500 p hp
  by_cases h505 : i < 510
  · exact Freiman.lowerHistory_bindings_0505_0510 i (by omega) h505 p hp
  by_cases h510 : i < 515
  · exact Freiman.lowerHistory_bindings_0510_0515 i (by omega) h510 p hp
  by_cases h515 : i < 520
  · exact Freiman.lowerHistory_bindings_0515_0520 i (by omega) h515 p hp
  by_cases h520 : i < 525
  · exact Freiman.lowerHistory_bindings_0520_0525 i (by omega) h520 p hp
  by_cases h525 : i < 530
  · exact Freiman.lowerHistory_bindings_0525_0530 i (by omega) h525 p hp
  by_cases h530 : i < 535
  · exact Freiman.lowerHistory_bindings_0530_0535 i (by omega) h530 p hp
  by_cases h535 : i < 540
  · exact Freiman.lowerHistory_bindings_0535_0540 i (by omega) h535 p hp
  by_cases h540 : i < 545
  · exact Freiman.lowerHistory_bindings_0540_0545 i (by omega) h540 p hp
  exact Freiman.lowerHistory_bindings_0545_0550 i (by omega) hhi p hp
#print axioms solution
