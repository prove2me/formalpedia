-- Prove2me | solution 1 for CKLaneA3X.Step027.row22
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:18:53.8656+00:00
-- url     : https://prove2.me/submissions/a8b14002-442d-417a-8212-add6908ba871

import Theorems.Thm_CKLaneA3X_Step027_row22_of_blocks
import Theorems.Thm_CKLaneA3X_Step027_row22_slots0_3
import Theorems.Thm_CKLaneA3X_Step027_row22_slots4_7
import Theorems.Thm_CKLaneA3X_Step027_row22_slots8_11
import Theorems.Thm_CKLaneA3X_Step027_row22_slots12_15
import Theorems.Thm_CKLaneA3X_Step027_row22_slots16_19
import Theorems.Thm_CKLaneA3X_Step027_row22_slots20_23
import Theorems.Thm_CKLaneA3X_Step027_row22_slots24_24
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (TPoly.mulT D_Us.P D_Us.P 24).getD 22 [] = D_UsUs.P.getD 22 [] := by
  apply CKLaneA3X.Step027.row22_of_blocks
  intro i
  fin_cases i
  · exact CKLaneA3X.Step027.row22_slots0_3 ⟨0, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots0_3 ⟨1, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots0_3 ⟨2, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots0_3 ⟨3, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots4_7 ⟨0, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots4_7 ⟨1, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots4_7 ⟨2, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots4_7 ⟨3, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots8_11 ⟨0, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots8_11 ⟨1, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots8_11 ⟨2, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots8_11 ⟨3, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots12_15 ⟨0, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots12_15 ⟨1, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots12_15 ⟨2, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots12_15 ⟨3, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots16_19 ⟨0, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots16_19 ⟨1, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots16_19 ⟨2, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots16_19 ⟨3, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots20_23 ⟨0, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots20_23 ⟨1, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots20_23 ⟨2, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots20_23 ⟨3, by decide⟩
  · exact CKLaneA3X.Step027.row22_slots24_24
