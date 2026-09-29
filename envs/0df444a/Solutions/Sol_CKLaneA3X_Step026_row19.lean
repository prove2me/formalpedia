-- Prove2me | solution 1 for CKLaneA3X.Step026.row19
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:28:51.049546+00:00
-- url     : https://prove2.me/submissions/3756b584-02b6-406f-8bdb-6ba117cca691

import Theorems.Thm_CKLaneA3X_Step026_row19_of_blocks
import Theorems.Thm_CKLaneA3X_Step026_row19_slots0_1
import Theorems.Thm_CKLaneA3X_Step026_row19_slots2_3
import Theorems.Thm_CKLaneA3X_Step026_row19_slots4_5
import Theorems.Thm_CKLaneA3X_Step026_row19_slots6_7
import Theorems.Thm_CKLaneA3X_Step026_row19_slots8_9
import Theorems.Thm_CKLaneA3X_Step026_row19_slots10_11
import Theorems.Thm_CKLaneA3X_Step026_row19_slots12_13
import Theorems.Thm_CKLaneA3X_Step026_row19_slots14_15
import Theorems.Thm_CKLaneA3X_Step026_row19_slots16_17
import Theorems.Thm_CKLaneA3X_Step026_row19_slots18_19
import Theorems.Thm_CKLaneA3X_Step026_row19_slots20_21
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24).getD 19 [] = D_mInner.P.getD 19 [] := by
  apply CKLaneA3X.Step026.row19_of_blocks
  intro i
  fin_cases i
  · exact CKLaneA3X.Step026.row19_slots0_1 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots0_1 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots2_3 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots2_3 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots4_5 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots4_5 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots6_7 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots6_7 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots8_9 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots8_9 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots10_11 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots10_11 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots12_13 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots12_13 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots14_15 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots14_15 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots16_17 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots16_17 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots18_19 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots18_19 ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots20_21 ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.row19_slots20_21 ⟨1, by decide⟩
