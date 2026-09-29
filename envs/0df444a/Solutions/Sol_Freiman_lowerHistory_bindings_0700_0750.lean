-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0700_0750
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T02:14:37.138369+00:00
-- url     : https://prove2.me/submissions/28b33a5c-b356-4dd4-9fc1-e9ec4ace9c0b

import Theorems.Thm_Freiman_lowerHistory_bindings_0700_0705
import Theorems.Thm_Freiman_lowerHistory_bindings_0705_0710
import Theorems.Thm_Freiman_lowerHistory_bindings_0710_0715
import Theorems.Thm_Freiman_lowerHistory_bindings_0715_0720
import Theorems.Thm_Freiman_lowerHistory_bindings_0720_0725
import Theorems.Thm_Freiman_lowerHistory_bindings_0725_0730
import Theorems.Thm_Freiman_lowerHistory_bindings_0730_0735
import Theorems.Thm_Freiman_lowerHistory_bindings_0735_0740
import Theorems.Thm_Freiman_lowerHistory_bindings_0740_0745
import Theorems.Thm_Freiman_lowerHistory_bindings_0745_0750
open Freiman
theorem solution : lowerHistoryBindingBatch 700 750 := by
  intro i hlo hhi p hp
  by_cases h700 : i < 705
  · exact Freiman.lowerHistory_bindings_0700_0705 i (by omega) h700 p hp
  by_cases h705 : i < 710
  · exact Freiman.lowerHistory_bindings_0705_0710 i (by omega) h705 p hp
  by_cases h710 : i < 715
  · exact Freiman.lowerHistory_bindings_0710_0715 i (by omega) h710 p hp
  by_cases h715 : i < 720
  · exact Freiman.lowerHistory_bindings_0715_0720 i (by omega) h715 p hp
  by_cases h720 : i < 725
  · exact Freiman.lowerHistory_bindings_0720_0725 i (by omega) h720 p hp
  by_cases h725 : i < 730
  · exact Freiman.lowerHistory_bindings_0725_0730 i (by omega) h725 p hp
  by_cases h730 : i < 735
  · exact Freiman.lowerHistory_bindings_0730_0735 i (by omega) h730 p hp
  by_cases h735 : i < 740
  · exact Freiman.lowerHistory_bindings_0735_0740 i (by omega) h735 p hp
  by_cases h740 : i < 745
  · exact Freiman.lowerHistory_bindings_0740_0745 i (by omega) h740 p hp
  exact Freiman.lowerHistory_bindings_0745_0750 i (by omega) hhi p hp
#print axioms solution
