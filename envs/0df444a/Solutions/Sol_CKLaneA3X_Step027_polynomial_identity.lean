-- Prove2me | solution 1 for CKLaneA3X.Step027.polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:24:35.04431+00:00
-- url     : https://prove2.me/submissions/c3f4dcb9-6079-437d-80a9-3ee147560cfa

import Theorems.Thm_CKLaneA3X_Step027_polynomial_of_rows
import Theorems.Thm_CKLaneA3X_Step027_empty_rows
import Theorems.Thm_CKLaneA3X_Step027_row2
import Theorems.Thm_CKLaneA3X_Step027_row4
import Theorems.Thm_CKLaneA3X_Step027_row6
import Theorems.Thm_CKLaneA3X_Step027_row8
import Theorems.Thm_CKLaneA3X_Step027_row10
import Theorems.Thm_CKLaneA3X_Step027_row12
import Theorems.Thm_CKLaneA3X_Step027_row14
import Theorems.Thm_CKLaneA3X_Step027_row16
import Theorems.Thm_CKLaneA3X_Step027_row18
import Theorems.Thm_CKLaneA3X_Step027_row20
import Theorems.Thm_CKLaneA3X_Step027_row22
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (TPoly.mulT D_Us.P D_Us.P 24) = D_UsUs.P := by
  apply CKLaneA3X.Step027.polynomial_of_rows
  intro i
  fin_cases i
  · exact CKLaneA3X.Step027.empty_rows ⟨0, by decide⟩
  · exact CKLaneA3X.Step027.empty_rows ⟨1, by decide⟩
  · exact CKLaneA3X.Step027.row2
  · exact CKLaneA3X.Step027.empty_rows ⟨2, by decide⟩
  · exact CKLaneA3X.Step027.row4
  · exact CKLaneA3X.Step027.empty_rows ⟨3, by decide⟩
  · exact CKLaneA3X.Step027.row6
  · exact CKLaneA3X.Step027.empty_rows ⟨4, by decide⟩
  · exact CKLaneA3X.Step027.row8
  · exact CKLaneA3X.Step027.empty_rows ⟨5, by decide⟩
  · exact CKLaneA3X.Step027.row10
  · exact CKLaneA3X.Step027.empty_rows ⟨6, by decide⟩
  · exact CKLaneA3X.Step027.row12
  · exact CKLaneA3X.Step027.empty_rows ⟨7, by decide⟩
  · exact CKLaneA3X.Step027.row14
  · exact CKLaneA3X.Step027.empty_rows ⟨8, by decide⟩
  · exact CKLaneA3X.Step027.row16
  · exact CKLaneA3X.Step027.empty_rows ⟨9, by decide⟩
  · exact CKLaneA3X.Step027.row18
  · exact CKLaneA3X.Step027.empty_rows ⟨10, by decide⟩
  · exact CKLaneA3X.Step027.row20
  · exact CKLaneA3X.Step027.empty_rows ⟨11, by decide⟩
  · exact CKLaneA3X.Step027.row22
  · exact CKLaneA3X.Step027.empty_rows ⟨12, by decide⟩
