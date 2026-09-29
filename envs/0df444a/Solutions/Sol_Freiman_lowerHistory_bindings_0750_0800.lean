-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0750_0800
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T02:35:35.299248+00:00
-- url     : https://prove2.me/submissions/737ebefa-ec7a-4e12-8b19-33d8c4f0e35d

import Theorems.Thm_Freiman_lowerHistory_bindings_0750_0755
import Theorems.Thm_Freiman_lowerHistory_bindings_0755_0760
import Theorems.Thm_Freiman_lowerHistory_bindings_0760_0765
import Theorems.Thm_Freiman_lowerHistory_bindings_0765_0770
import Theorems.Thm_Freiman_lowerHistory_bindings_0770_0775
import Theorems.Thm_Freiman_lowerHistory_bindings_0775_0780
import Theorems.Thm_Freiman_lowerHistory_bindings_0780_0785
import Theorems.Thm_Freiman_lowerHistory_bindings_0785_0790
import Theorems.Thm_Freiman_lowerHistory_bindings_0790_0795
import Theorems.Thm_Freiman_lowerHistory_bindings_0795_0800
open Freiman
theorem solution : lowerHistoryBindingBatch 750 800 := by
  intro i hlo hhi p hp
  by_cases h750 : i < 755
  · exact Freiman.lowerHistory_bindings_0750_0755 i (by omega) h750 p hp
  by_cases h755 : i < 760
  · exact Freiman.lowerHistory_bindings_0755_0760 i (by omega) h755 p hp
  by_cases h760 : i < 765
  · exact Freiman.lowerHistory_bindings_0760_0765 i (by omega) h760 p hp
  by_cases h765 : i < 770
  · exact Freiman.lowerHistory_bindings_0765_0770 i (by omega) h765 p hp
  by_cases h770 : i < 775
  · exact Freiman.lowerHistory_bindings_0770_0775 i (by omega) h770 p hp
  by_cases h775 : i < 780
  · exact Freiman.lowerHistory_bindings_0775_0780 i (by omega) h775 p hp
  by_cases h780 : i < 785
  · exact Freiman.lowerHistory_bindings_0780_0785 i (by omega) h780 p hp
  by_cases h785 : i < 790
  · exact Freiman.lowerHistory_bindings_0785_0790 i (by omega) h785 p hp
  by_cases h790 : i < 795
  · exact Freiman.lowerHistory_bindings_0790_0795 i (by omega) h790 p hp
  exact Freiman.lowerHistory_bindings_0795_0800 i (by omega) hhi p hp
#print axioms solution
