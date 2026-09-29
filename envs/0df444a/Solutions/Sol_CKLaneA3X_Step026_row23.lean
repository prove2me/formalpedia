-- Prove2me | solution 1 for CKLaneA3X.Step026.row23
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:47:57.446812+00:00
-- url     : https://prove2.me/submissions/354574e7-dffa-40b7-ae2c-357767588faa

import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Theorems.Thm_CKLaneA3X_Step026_row23_of_blocks
import Theorems.Thm_CKLaneA3X_Step026_row23_slot0
import Theorems.Thm_CKLaneA3X_Step026_row23_slot1
import Theorems.Thm_CKLaneA3X_Step026_row23_slot2
import Theorems.Thm_CKLaneA3X_Step026_row23_slot3
import Theorems.Thm_CKLaneA3X_Step026_row23_slot4
import Theorems.Thm_CKLaneA3X_Step026_row23_slot5
import Theorems.Thm_CKLaneA3X_Step026_row23_slot6
import Theorems.Thm_CKLaneA3X_Step026_row23_slot7
import Theorems.Thm_CKLaneA3X_Step026_row23_slot8
import Theorems.Thm_CKLaneA3X_Step026_row23_slot9
import Theorems.Thm_CKLaneA3X_Step026_row23_slot10
import Theorems.Thm_CKLaneA3X_Step026_row23_slot11
import Theorems.Thm_CKLaneA3X_Step026_row23_slot12
import Theorems.Thm_CKLaneA3X_Step026_row23_slot13
import Theorems.Thm_CKLaneA3X_Step026_row23_slot14
import Theorems.Thm_CKLaneA3X_Step026_row23_slot15
import Theorems.Thm_CKLaneA3X_Step026_row23_slot16
import Theorems.Thm_CKLaneA3X_Step026_row23_slot17
import Theorems.Thm_CKLaneA3X_Step026_row23_slot18
import Theorems.Thm_CKLaneA3X_Step026_row23_slot19
import Theorems.Thm_CKLaneA3X_Step026_row23_slot20
import Theorems.Thm_CKLaneA3X_Step026_row23_slot21
import Theorems.Thm_CKLaneA3X_Step026_row23_slot22
import Theorems.Thm_CKLaneA3X_Step026_row23_slot23
import Theorems.Thm_CKLaneA3X_Step026_row23_slot24
import Theorems.Thm_CKLaneA3X_Step026_row23_sigma25
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24).getD 23 [] = D_mInner.P.getD 23 [] := by
  apply CKLaneA3X.Step026.row23_of_blocks
  intro i
  fin_cases i
  · exact CKLaneA3X.Step026.row23_slot0
  · exact CKLaneA3X.Step026.row23_slot1
  · exact CKLaneA3X.Step026.row23_slot2
  · exact CKLaneA3X.Step026.row23_slot3
  · exact CKLaneA3X.Step026.row23_slot4
  · exact CKLaneA3X.Step026.row23_slot5
  · exact CKLaneA3X.Step026.row23_slot6
  · exact CKLaneA3X.Step026.row23_slot7
  · exact CKLaneA3X.Step026.row23_slot8
  · exact CKLaneA3X.Step026.row23_slot9
  · exact CKLaneA3X.Step026.row23_slot10
  · exact CKLaneA3X.Step026.row23_slot11
  · exact CKLaneA3X.Step026.row23_slot12
  · exact CKLaneA3X.Step026.row23_slot13
  · exact CKLaneA3X.Step026.row23_slot14
  · exact CKLaneA3X.Step026.row23_slot15
  · exact CKLaneA3X.Step026.row23_slot16
  · exact CKLaneA3X.Step026.row23_slot17
  · exact CKLaneA3X.Step026.row23_slot18
  · exact CKLaneA3X.Step026.row23_slot19
  · exact CKLaneA3X.Step026.row23_slot20
  · exact CKLaneA3X.Step026.row23_slot21
  · exact CKLaneA3X.Step026.row23_slot22
  · exact CKLaneA3X.Step026.row23_slot23
  · exact CKLaneA3X.Step026.row23_slot24
  · exact CKLaneA3X.Step026.row23_sigma25
