-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepSum.span_bAllR_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:18:48.979543+00:00
-- url     : https://prove2.me/submissions/0d4e1f25-c110-498d-9812-e7b0ad305051

-- Generated from ChapterLorentzRealRepSum.lean — solution of BookProof.ChapterLorentzRealRepSum.span_bAllR_eq
import Mathlib
import Definitions.Def_ChapterLorentzRealRepSum
import Theorems.Thm_BookProof_ChapterLorentzRealRepSum_range_bAllR
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open Module

set_option maxHeartbeats 1000000 in
theorem solution :
    Submodule.span ℝ (Set.range bAllR) = WHalf ⊔ W10 ⊔ WPs := by

  rw [range_bAllR, Submodule.span_union, Submodule.span_union]
  rfl
