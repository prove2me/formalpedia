-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepSum.finrank_sup
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:19:46.755998+00:00
-- url     : https://prove2.me/submissions/f3a343bb-6a1b-4a55-9ded-c880294b51e6

-- Generated from ChapterLorentzRealRepSum.lean — solution of BookProof.ChapterLorentzRealRepSum.finrank_sup
import Mathlib
import Definitions.Def_ChapterLorentzRealRepSum
import Theorems.Thm_BookProof_ChapterLorentzRealRepSum_bAllR_linearIndependent
import Theorems.Thm_BookProof_ChapterLorentzRealRepSum_span_bAllR_eq
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open Module

set_option maxHeartbeats 1000000 in
theorem solution : finrank ℝ ↥(WHalf ⊔ W10 ⊔ WPs) = 14 := by

  have := finrank_span_eq_card bAllR_linearIndependent
  rw [span_bAllR_eq] at this
  simpa using this
