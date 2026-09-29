-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0400_0450
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T23:07:52.573632+00:00
-- url     : https://prove2.me/submissions/5ce92e15-cfde-47d1-b82b-af60d96d1d0a

import Theorems.Thm_Freiman_lowerHistory_bindings_0400_0405
import Theorems.Thm_Freiman_lowerHistory_bindings_0405_0410
import Theorems.Thm_Freiman_lowerHistory_bindings_0410_0415
import Theorems.Thm_Freiman_lowerHistory_bindings_0415_0420
import Theorems.Thm_Freiman_lowerHistory_bindings_0420_0425
import Theorems.Thm_Freiman_lowerHistory_bindings_0425_0430
import Theorems.Thm_Freiman_lowerHistory_bindings_0430_0435
import Theorems.Thm_Freiman_lowerHistory_bindings_0435_0440
import Theorems.Thm_Freiman_lowerHistory_bindings_0440_0445
import Theorems.Thm_Freiman_lowerHistory_bindings_0445_0450
open Freiman
theorem solution : lowerHistoryBindingBatch 400 450 := by
  intro i hlo hhi p hp
  by_cases h400 : i < 405
  · exact Freiman.lowerHistory_bindings_0400_0405 i (by omega) h400 p hp
  by_cases h405 : i < 410
  · exact Freiman.lowerHistory_bindings_0405_0410 i (by omega) h405 p hp
  by_cases h410 : i < 415
  · exact Freiman.lowerHistory_bindings_0410_0415 i (by omega) h410 p hp
  by_cases h415 : i < 420
  · exact Freiman.lowerHistory_bindings_0415_0420 i (by omega) h415 p hp
  by_cases h420 : i < 425
  · exact Freiman.lowerHistory_bindings_0420_0425 i (by omega) h420 p hp
  by_cases h425 : i < 430
  · exact Freiman.lowerHistory_bindings_0425_0430 i (by omega) h425 p hp
  by_cases h430 : i < 435
  · exact Freiman.lowerHistory_bindings_0430_0435 i (by omega) h430 p hp
  by_cases h435 : i < 440
  · exact Freiman.lowerHistory_bindings_0435_0440 i (by omega) h435 p hp
  by_cases h440 : i < 445
  · exact Freiman.lowerHistory_bindings_0440_0445 i (by omega) h440 p hp
  exact Freiman.lowerHistory_bindings_0445_0450 i (by omega) hhi p hp
#print axioms solution
