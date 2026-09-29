-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0450_0500
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T23:29:43.180623+00:00
-- url     : https://prove2.me/submissions/f2906768-856e-47bb-b17d-281acbbbb3f1

import Theorems.Thm_Freiman_lowerHistory_bindings_0450_0455
import Theorems.Thm_Freiman_lowerHistory_bindings_0455_0460
import Theorems.Thm_Freiman_lowerHistory_bindings_0460_0465
import Theorems.Thm_Freiman_lowerHistory_bindings_0465_0470
import Theorems.Thm_Freiman_lowerHistory_bindings_0470_0475
import Theorems.Thm_Freiman_lowerHistory_bindings_0475_0480
import Theorems.Thm_Freiman_lowerHistory_bindings_0480_0485
import Theorems.Thm_Freiman_lowerHistory_bindings_0485_0490
import Theorems.Thm_Freiman_lowerHistory_bindings_0490_0495
import Theorems.Thm_Freiman_lowerHistory_bindings_0495_0500
open Freiman
theorem solution : lowerHistoryBindingBatch 450 500 := by
  intro i hlo hhi p hp
  by_cases h450 : i < 455
  · exact Freiman.lowerHistory_bindings_0450_0455 i (by omega) h450 p hp
  by_cases h455 : i < 460
  · exact Freiman.lowerHistory_bindings_0455_0460 i (by omega) h455 p hp
  by_cases h460 : i < 465
  · exact Freiman.lowerHistory_bindings_0460_0465 i (by omega) h460 p hp
  by_cases h465 : i < 470
  · exact Freiman.lowerHistory_bindings_0465_0470 i (by omega) h465 p hp
  by_cases h470 : i < 475
  · exact Freiman.lowerHistory_bindings_0470_0475 i (by omega) h470 p hp
  by_cases h475 : i < 480
  · exact Freiman.lowerHistory_bindings_0475_0480 i (by omega) h475 p hp
  by_cases h480 : i < 485
  · exact Freiman.lowerHistory_bindings_0480_0485 i (by omega) h480 p hp
  by_cases h485 : i < 490
  · exact Freiman.lowerHistory_bindings_0485_0490 i (by omega) h485 p hp
  by_cases h490 : i < 495
  · exact Freiman.lowerHistory_bindings_0490_0495 i (by omega) h490 p hp
  exact Freiman.lowerHistory_bindings_0495_0500 i (by omega) hhi p hp
#print axioms solution
