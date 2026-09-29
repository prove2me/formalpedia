-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0550_0600
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T00:55:12.412269+00:00
-- url     : https://prove2.me/submissions/79dabb6a-2cb1-4c64-b707-04fec66113df

import Theorems.Thm_Freiman_lowerHistory_bindings_0550_0555
import Theorems.Thm_Freiman_lowerHistory_bindings_0555_0560
import Theorems.Thm_Freiman_lowerHistory_bindings_0560_0565
import Theorems.Thm_Freiman_lowerHistory_bindings_0565_0570
import Theorems.Thm_Freiman_lowerHistory_bindings_0570_0575
import Theorems.Thm_Freiman_lowerHistory_bindings_0575_0580
import Theorems.Thm_Freiman_lowerHistory_bindings_0580_0585
import Theorems.Thm_Freiman_lowerHistory_bindings_0585_0590
import Theorems.Thm_Freiman_lowerHistory_bindings_0590_0595
import Theorems.Thm_Freiman_lowerHistory_bindings_0595_0600
open Freiman
theorem solution : lowerHistoryBindingBatch 550 600 := by
  intro i hlo hhi p hp
  by_cases h550 : i < 555
  · exact Freiman.lowerHistory_bindings_0550_0555 i (by omega) h550 p hp
  by_cases h555 : i < 560
  · exact Freiman.lowerHistory_bindings_0555_0560 i (by omega) h555 p hp
  by_cases h560 : i < 565
  · exact Freiman.lowerHistory_bindings_0560_0565 i (by omega) h560 p hp
  by_cases h565 : i < 570
  · exact Freiman.lowerHistory_bindings_0565_0570 i (by omega) h565 p hp
  by_cases h570 : i < 575
  · exact Freiman.lowerHistory_bindings_0570_0575 i (by omega) h570 p hp
  by_cases h575 : i < 580
  · exact Freiman.lowerHistory_bindings_0575_0580 i (by omega) h575 p hp
  by_cases h580 : i < 585
  · exact Freiman.lowerHistory_bindings_0580_0585 i (by omega) h580 p hp
  by_cases h585 : i < 590
  · exact Freiman.lowerHistory_bindings_0585_0590 i (by omega) h585 p hp
  by_cases h590 : i < 595
  · exact Freiman.lowerHistory_bindings_0590_0595 i (by omega) h590 p hp
  exact Freiman.lowerHistory_bindings_0595_0600 i (by omega) hhi p hp
#print axioms solution
