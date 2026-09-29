-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0950_1000
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T03:59:09.11104+00:00
-- url     : https://prove2.me/submissions/455ba954-479e-4d9a-bb6a-1ef10c580867

import Theorems.Thm_Freiman_lowerHistory_bindings_0950_0955
import Theorems.Thm_Freiman_lowerHistory_bindings_0955_0960
import Theorems.Thm_Freiman_lowerHistory_bindings_0960_0965
import Theorems.Thm_Freiman_lowerHistory_bindings_0965_0970
import Theorems.Thm_Freiman_lowerHistory_bindings_0970_0975
import Theorems.Thm_Freiman_lowerHistory_bindings_0975_0980
import Theorems.Thm_Freiman_lowerHistory_bindings_0980_0985
import Theorems.Thm_Freiman_lowerHistory_bindings_0985_0990
import Theorems.Thm_Freiman_lowerHistory_bindings_0990_0995
import Theorems.Thm_Freiman_lowerHistory_bindings_0995_1000
open Freiman
theorem solution : lowerHistoryBindingBatch 950 1000 := by
  intro i hlo hhi p hp
  by_cases h950 : i < 955
  · exact Freiman.lowerHistory_bindings_0950_0955 i (by omega) h950 p hp
  by_cases h955 : i < 960
  · exact Freiman.lowerHistory_bindings_0955_0960 i (by omega) h955 p hp
  by_cases h960 : i < 965
  · exact Freiman.lowerHistory_bindings_0960_0965 i (by omega) h960 p hp
  by_cases h965 : i < 970
  · exact Freiman.lowerHistory_bindings_0965_0970 i (by omega) h965 p hp
  by_cases h970 : i < 975
  · exact Freiman.lowerHistory_bindings_0970_0975 i (by omega) h970 p hp
  by_cases h975 : i < 980
  · exact Freiman.lowerHistory_bindings_0975_0980 i (by omega) h975 p hp
  by_cases h980 : i < 985
  · exact Freiman.lowerHistory_bindings_0980_0985 i (by omega) h980 p hp
  by_cases h985 : i < 990
  · exact Freiman.lowerHistory_bindings_0985_0990 i (by omega) h985 p hp
  by_cases h990 : i < 995
  · exact Freiman.lowerHistory_bindings_0990_0995 i (by omega) h990 p hp
  exact Freiman.lowerHistory_bindings_0995_1000 i (by omega) hhi p hp
#print axioms solution
