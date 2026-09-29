-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0600_0650
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T01:19:26.461527+00:00
-- url     : https://prove2.me/submissions/9c9e23ca-ec66-4ba9-be48-f1ecd11f2e0d

import Theorems.Thm_Freiman_lowerHistory_bindings_0600_0605
import Theorems.Thm_Freiman_lowerHistory_bindings_0605_0610
import Theorems.Thm_Freiman_lowerHistory_bindings_0610_0615
import Theorems.Thm_Freiman_lowerHistory_bindings_0615_0620
import Theorems.Thm_Freiman_lowerHistory_bindings_0620_0625
import Theorems.Thm_Freiman_lowerHistory_bindings_0625_0630
import Theorems.Thm_Freiman_lowerHistory_bindings_0630_0635
import Theorems.Thm_Freiman_lowerHistory_bindings_0635_0640
import Theorems.Thm_Freiman_lowerHistory_bindings_0640_0645
import Theorems.Thm_Freiman_lowerHistory_bindings_0645_0650
open Freiman
theorem solution : lowerHistoryBindingBatch 600 650 := by
  intro i hlo hhi p hp
  by_cases h600 : i < 605
  · exact Freiman.lowerHistory_bindings_0600_0605 i (by omega) h600 p hp
  by_cases h605 : i < 610
  · exact Freiman.lowerHistory_bindings_0605_0610 i (by omega) h605 p hp
  by_cases h610 : i < 615
  · exact Freiman.lowerHistory_bindings_0610_0615 i (by omega) h610 p hp
  by_cases h615 : i < 620
  · exact Freiman.lowerHistory_bindings_0615_0620 i (by omega) h615 p hp
  by_cases h620 : i < 625
  · exact Freiman.lowerHistory_bindings_0620_0625 i (by omega) h620 p hp
  by_cases h625 : i < 630
  · exact Freiman.lowerHistory_bindings_0625_0630 i (by omega) h625 p hp
  by_cases h630 : i < 635
  · exact Freiman.lowerHistory_bindings_0630_0635 i (by omega) h630 p hp
  by_cases h635 : i < 640
  · exact Freiman.lowerHistory_bindings_0635_0640 i (by omega) h635 p hp
  by_cases h640 : i < 645
  · exact Freiman.lowerHistory_bindings_0640_0645 i (by omega) h640 p hp
  exact Freiman.lowerHistory_bindings_0645_0650 i (by omega) hhi p hp
#print axioms solution
