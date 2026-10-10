-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepFull.span_bFullR_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:09:52.323052+00:00
-- url     : https://prove2.me/submissions/4872667c-2a2c-4203-895a-07867eee5f23

-- Generated from ChapterLorentzRealRepFull.lean — solution of BookProof.ChapterLorentzRealRepFull.span_bFullR_eq
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
import Theorems.Thm_BookProof_ChapterLorentzRealRepFull_range_bFullR
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepFull



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum
open Module

set_option maxHeartbeats 1000000 in
theorem solution :
    Submodule.span ℝ (Set.range bFullR) = WHalf ⊔ W10 ⊔ WPs ⊔ WTwo := by

  rw [range_bFullR, Submodule.span_union, Submodule.span_union, Submodule.span_union]
  rfl
