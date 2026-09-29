-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0650_0700
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T01:55:14.088077+00:00
-- url     : https://prove2.me/submissions/673c61eb-c05d-42ec-924b-944a6389c751

import Theorems.Thm_Freiman_lowerHistory_bindings_0650_0655
import Theorems.Thm_Freiman_lowerHistory_bindings_0655_0660
import Theorems.Thm_Freiman_lowerHistory_bindings_0660_0665
import Theorems.Thm_Freiman_lowerHistory_bindings_0665_0670
import Theorems.Thm_Freiman_lowerHistory_bindings_0670_0675
import Theorems.Thm_Freiman_lowerHistory_bindings_0675_0680
import Theorems.Thm_Freiman_lowerHistory_bindings_0680_0685
import Theorems.Thm_Freiman_lowerHistory_bindings_0685_0690
import Theorems.Thm_Freiman_lowerHistory_bindings_0690_0695
import Theorems.Thm_Freiman_lowerHistory_bindings_0695_0700
open Freiman
theorem solution : lowerHistoryBindingBatch 650 700 := by
  intro i hlo hhi p hp
  by_cases h650 : i < 655
  · exact Freiman.lowerHistory_bindings_0650_0655 i (by omega) h650 p hp
  by_cases h655 : i < 660
  · exact Freiman.lowerHistory_bindings_0655_0660 i (by omega) h655 p hp
  by_cases h660 : i < 665
  · exact Freiman.lowerHistory_bindings_0660_0665 i (by omega) h660 p hp
  by_cases h665 : i < 670
  · exact Freiman.lowerHistory_bindings_0665_0670 i (by omega) h665 p hp
  by_cases h670 : i < 675
  · exact Freiman.lowerHistory_bindings_0670_0675 i (by omega) h670 p hp
  by_cases h675 : i < 680
  · exact Freiman.lowerHistory_bindings_0675_0680 i (by omega) h675 p hp
  by_cases h680 : i < 685
  · exact Freiman.lowerHistory_bindings_0680_0685 i (by omega) h680 p hp
  by_cases h685 : i < 690
  · exact Freiman.lowerHistory_bindings_0685_0690 i (by omega) h685 p hp
  by_cases h690 : i < 695
  · exact Freiman.lowerHistory_bindings_0690_0695 i (by omega) h690 p hp
  exact Freiman.lowerHistory_bindings_0695_0700 i (by omega) hhi p hp
#print axioms solution
