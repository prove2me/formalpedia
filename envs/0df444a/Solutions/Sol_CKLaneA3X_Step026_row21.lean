-- Prove2me | solution 1 for CKLaneA3X.Step026.row21
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:29:04.738709+00:00
-- url     : https://prove2.me/submissions/c6dcd859-3799-4878-ac4b-667f0e35a8a3

import Theorems.Thm_CKLaneA3X_Step026_row21_of_blocks
import Theorems.Thm_CKLaneA3X_Step026_row21_slots0_1
import Theorems.Thm_CKLaneA3X_Step026_row21_slots2_3
import Theorems.Thm_CKLaneA3X_Step026_row21_slots4_5
import Theorems.Thm_CKLaneA3X_Step026_row21_slots6_7
import Theorems.Thm_CKLaneA3X_Step026_row21_slots8_9
import Theorems.Thm_CKLaneA3X_Step026_row21_slots10_11
import Theorems.Thm_CKLaneA3X_Step026_row21_slots12_13
import Theorems.Thm_CKLaneA3X_Step026_row21_slots14_15
import Theorems.Thm_CKLaneA3X_Step026_row21_slots16_17
import Theorems.Thm_CKLaneA3X_Step026_row21_slots18_19
import Theorems.Thm_CKLaneA3X_Step026_row21_slots20_21
import Theorems.Thm_CKLaneA3X_Step026_row21_slots22_23
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24).getD 21 [] = D_mInner.P.getD 21 [] := by
  apply CKLaneA3X.Step026.row21_of_blocks
  intro i
  fin_cases i
  · exact CKLaneA3X.Step026.row21_slots0_1 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots0_1 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots2_3 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots2_3 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots4_5 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots4_5 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots6_7 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots6_7 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots8_9 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots8_9 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots10_11 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots10_11 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots12_13 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots12_13 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots14_15 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots14_15 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots16_17 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots16_17 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots18_19 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots18_19 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots20_21 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots20_21 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots22_23 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row21_slots22_23 ⟨1, by decide⟩
