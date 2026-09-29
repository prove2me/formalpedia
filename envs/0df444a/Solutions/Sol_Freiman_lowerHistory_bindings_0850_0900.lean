-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0850_0900
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T03:17:18.220512+00:00
-- url     : https://prove2.me/submissions/acf3937b-3177-4703-89fd-0a2cd6e78f39

import Theorems.Thm_Freiman_lowerHistory_bindings_0850_0855
import Theorems.Thm_Freiman_lowerHistory_bindings_0855_0860
import Theorems.Thm_Freiman_lowerHistory_bindings_0860_0865
import Theorems.Thm_Freiman_lowerHistory_bindings_0865_0870
import Theorems.Thm_Freiman_lowerHistory_bindings_0870_0875
import Theorems.Thm_Freiman_lowerHistory_bindings_0875_0880
import Theorems.Thm_Freiman_lowerHistory_bindings_0880_0885
import Theorems.Thm_Freiman_lowerHistory_bindings_0885_0890
import Theorems.Thm_Freiman_lowerHistory_bindings_0890_0895
import Theorems.Thm_Freiman_lowerHistory_bindings_0895_0900
open Freiman
theorem solution : lowerHistoryBindingBatch 850 900 := by
  intro i hlo hhi p hp
  by_cases h850 : i < 855
  · exact Freiman.lowerHistory_bindings_0850_0855 i (by omega) h850 p hp
  by_cases h855 : i < 860
  · exact Freiman.lowerHistory_bindings_0855_0860 i (by omega) h855 p hp
  by_cases h860 : i < 865
  · exact Freiman.lowerHistory_bindings_0860_0865 i (by omega) h860 p hp
  by_cases h865 : i < 870
  · exact Freiman.lowerHistory_bindings_0865_0870 i (by omega) h865 p hp
  by_cases h870 : i < 875
  · exact Freiman.lowerHistory_bindings_0870_0875 i (by omega) h870 p hp
  by_cases h875 : i < 880
  · exact Freiman.lowerHistory_bindings_0875_0880 i (by omega) h875 p hp
  by_cases h880 : i < 885
  · exact Freiman.lowerHistory_bindings_0880_0885 i (by omega) h880 p hp
  by_cases h885 : i < 890
  · exact Freiman.lowerHistory_bindings_0885_0890 i (by omega) h885 p hp
  by_cases h890 : i < 895
  · exact Freiman.lowerHistory_bindings_0890_0895 i (by omega) h890 p hp
  exact Freiman.lowerHistory_bindings_0895_0900 i (by omega) hhi p hp
#print axioms solution
