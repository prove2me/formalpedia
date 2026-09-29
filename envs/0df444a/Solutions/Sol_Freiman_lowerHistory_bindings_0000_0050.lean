-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0000_0050
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-15T20:52:41.388177+00:00
-- url     : https://prove2.me/submissions/b28c78f2-c6ce-447a-846c-07e088adb680

import Theorems.Thm_Freiman_lowerHistory_bindings_0000_0005
import Theorems.Thm_Freiman_lowerHistory_bindings_0005_0010
import Theorems.Thm_Freiman_lowerHistory_bindings_0010_0015
import Theorems.Thm_Freiman_lowerHistory_bindings_0015_0020
import Theorems.Thm_Freiman_lowerHistory_bindings_0020_0025
import Theorems.Thm_Freiman_lowerHistory_bindings_0025_0030
import Theorems.Thm_Freiman_lowerHistory_bindings_0030_0035
import Theorems.Thm_Freiman_lowerHistory_bindings_0035_0040
import Theorems.Thm_Freiman_lowerHistory_bindings_0040_0045
import Theorems.Thm_Freiman_lowerHistory_bindings_0045_0050
open Freiman
set_option autoImplicit false

-- Partition the original batch using existing five-path lemmas.
theorem solution : lowerHistoryBindingBatch 0 50 := by
  intro i hlo hhi p hp
  by_cases h5 : i < 5
  · exact lowerHistory_bindings_0000_0005 i hlo h5 p hp
  by_cases h10 : i < 10
  · exact lowerHistory_bindings_0005_0010 i (by omega) h10 p hp
  by_cases h15 : i < 15
  · exact lowerHistory_bindings_0010_0015 i (by omega) h15 p hp
  by_cases h20 : i < 20
  · exact lowerHistory_bindings_0015_0020 i (by omega) h20 p hp
  by_cases h25 : i < 25
  · exact lowerHistory_bindings_0020_0025 i (by omega) h25 p hp
  by_cases h30 : i < 30
  · exact lowerHistory_bindings_0025_0030 i (by omega) h30 p hp
  by_cases h35 : i < 35
  · exact lowerHistory_bindings_0030_0035 i (by omega) h35 p hp
  by_cases h40 : i < 40
  · exact lowerHistory_bindings_0035_0040 i (by omega) h40 p hp
  by_cases h45 : i < 45
  · exact lowerHistory_bindings_0040_0045 i (by omega) h45 p hp
  exact lowerHistory_bindings_0045_0050 i (by omega) hhi p hp
