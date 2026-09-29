-- Prove2me | solution 1 for CKLaneA3X.Step026.polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:33:54.233049+00:00
-- url     : https://prove2.me/submissions/9b2e6402-8c26-4451-a412-d47a063dacd8

import Theorems.Thm_CKLaneA3X_Step026_polynomial_of_rows
import Theorems.Thm_CKLaneA3X_Step026_empty_rows
import Theorems.Thm_CKLaneA3X_Step026_row3
import Theorems.Thm_CKLaneA3X_Step026_row5
import Theorems.Thm_CKLaneA3X_Step026_row7
import Theorems.Thm_CKLaneA3X_Step026_row9
import Theorems.Thm_CKLaneA3X_Step026_row11
import Theorems.Thm_CKLaneA3X_Step026_row13
import Theorems.Thm_CKLaneA3X_Step026_row15
import Theorems.Thm_CKLaneA3X_Step026_row17
import Theorems.Thm_CKLaneA3X_Step026_row19
import Theorems.Thm_CKLaneA3X_Step026_row21
import Theorems.Thm_CKLaneA3X_Step026_row23
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24) = D_mInner.P := by
  apply CKLaneA3X.Step026.polynomial_of_rows
  intro i
  fin_cases i
  · exact CKLaneA3X.Step026.empty_rows ⟨0, by decide⟩
  · exact CKLaneA3X.Step026.empty_rows ⟨1, by decide⟩
  · exact CKLaneA3X.Step026.empty_rows ⟨2, by decide⟩
  · exact CKLaneA3X.Step026.row3
  · exact CKLaneA3X.Step026.empty_rows ⟨3, by decide⟩
  · exact CKLaneA3X.Step026.row5
  · exact CKLaneA3X.Step026.empty_rows ⟨4, by decide⟩
  · exact CKLaneA3X.Step026.row7
  · exact CKLaneA3X.Step026.empty_rows ⟨5, by decide⟩
  · exact CKLaneA3X.Step026.row9
  · exact CKLaneA3X.Step026.empty_rows ⟨6, by decide⟩
  · exact CKLaneA3X.Step026.row11
  · exact CKLaneA3X.Step026.empty_rows ⟨7, by decide⟩
  · exact CKLaneA3X.Step026.row13
  · exact CKLaneA3X.Step026.empty_rows ⟨8, by decide⟩
  · exact CKLaneA3X.Step026.row15
  · exact CKLaneA3X.Step026.empty_rows ⟨9, by decide⟩
  · exact CKLaneA3X.Step026.row17
  · exact CKLaneA3X.Step026.empty_rows ⟨10, by decide⟩
  · exact CKLaneA3X.Step026.row19
  · exact CKLaneA3X.Step026.empty_rows ⟨11, by decide⟩
  · exact CKLaneA3X.Step026.row21
  · exact CKLaneA3X.Step026.empty_rows ⟨12, by decide⟩
  · exact CKLaneA3X.Step026.row23
