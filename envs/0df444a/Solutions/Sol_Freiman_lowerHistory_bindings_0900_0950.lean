-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0900_0950
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T03:38:39.569686+00:00
-- url     : https://prove2.me/submissions/6674bf42-ebe8-47a7-975f-030e19de49fa

import Theorems.Thm_Freiman_lowerHistory_bindings_0900_0905
import Theorems.Thm_Freiman_lowerHistory_bindings_0905_0910
import Theorems.Thm_Freiman_lowerHistory_bindings_0910_0915
import Theorems.Thm_Freiman_lowerHistory_bindings_0915_0920
import Theorems.Thm_Freiman_lowerHistory_bindings_0920_0925
import Theorems.Thm_Freiman_lowerHistory_bindings_0925_0930
import Theorems.Thm_Freiman_lowerHistory_bindings_0930_0935
import Theorems.Thm_Freiman_lowerHistory_bindings_0935_0940
import Theorems.Thm_Freiman_lowerHistory_bindings_0940_0945
import Theorems.Thm_Freiman_lowerHistory_bindings_0945_0950
open Freiman
theorem solution : lowerHistoryBindingBatch 900 950 := by
  intro i hlo hhi p hp
  by_cases h900 : i < 905
  · exact Freiman.lowerHistory_bindings_0900_0905 i (by omega) h900 p hp
  by_cases h905 : i < 910
  · exact Freiman.lowerHistory_bindings_0905_0910 i (by omega) h905 p hp
  by_cases h910 : i < 915
  · exact Freiman.lowerHistory_bindings_0910_0915 i (by omega) h910 p hp
  by_cases h915 : i < 920
  · exact Freiman.lowerHistory_bindings_0915_0920 i (by omega) h915 p hp
  by_cases h920 : i < 925
  · exact Freiman.lowerHistory_bindings_0920_0925 i (by omega) h920 p hp
  by_cases h925 : i < 930
  · exact Freiman.lowerHistory_bindings_0925_0930 i (by omega) h925 p hp
  by_cases h930 : i < 935
  · exact Freiman.lowerHistory_bindings_0930_0935 i (by omega) h930 p hp
  by_cases h935 : i < 940
  · exact Freiman.lowerHistory_bindings_0935_0940 i (by omega) h935 p hp
  by_cases h940 : i < 945
  · exact Freiman.lowerHistory_bindings_0940_0945 i (by omega) h940 p hp
  exact Freiman.lowerHistory_bindings_0945_0950 i (by omega) hhi p hp
#print axioms solution
