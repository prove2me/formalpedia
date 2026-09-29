-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0800_0850
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T02:56:35.739887+00:00
-- url     : https://prove2.me/submissions/91f825d6-b265-44e1-ac37-771750302c38

import Theorems.Thm_Freiman_lowerHistory_bindings_0800_0805
import Theorems.Thm_Freiman_lowerHistory_bindings_0805_0810
import Theorems.Thm_Freiman_lowerHistory_bindings_0810_0815
import Theorems.Thm_Freiman_lowerHistory_bindings_0815_0820
import Theorems.Thm_Freiman_lowerHistory_bindings_0820_0825
import Theorems.Thm_Freiman_lowerHistory_bindings_0825_0830
import Theorems.Thm_Freiman_lowerHistory_bindings_0830_0835
import Theorems.Thm_Freiman_lowerHistory_bindings_0835_0840
import Theorems.Thm_Freiman_lowerHistory_bindings_0840_0845
import Theorems.Thm_Freiman_lowerHistory_bindings_0845_0850
open Freiman
theorem solution : lowerHistoryBindingBatch 800 850 := by
  intro i hlo hhi p hp
  by_cases h800 : i < 805
  · exact Freiman.lowerHistory_bindings_0800_0805 i (by omega) h800 p hp
  by_cases h805 : i < 810
  · exact Freiman.lowerHistory_bindings_0805_0810 i (by omega) h805 p hp
  by_cases h810 : i < 815
  · exact Freiman.lowerHistory_bindings_0810_0815 i (by omega) h810 p hp
  by_cases h815 : i < 820
  · exact Freiman.lowerHistory_bindings_0815_0820 i (by omega) h815 p hp
  by_cases h820 : i < 825
  · exact Freiman.lowerHistory_bindings_0820_0825 i (by omega) h820 p hp
  by_cases h825 : i < 830
  · exact Freiman.lowerHistory_bindings_0825_0830 i (by omega) h825 p hp
  by_cases h830 : i < 835
  · exact Freiman.lowerHistory_bindings_0830_0835 i (by omega) h830 p hp
  by_cases h835 : i < 840
  · exact Freiman.lowerHistory_bindings_0835_0840 i (by omega) h835 p hp
  by_cases h840 : i < 845
  · exact Freiman.lowerHistory_bindings_0840_0845 i (by omega) h840 p hp
  exact Freiman.lowerHistory_bindings_0845_0850 i (by omega) hhi p hp
#print axioms solution
