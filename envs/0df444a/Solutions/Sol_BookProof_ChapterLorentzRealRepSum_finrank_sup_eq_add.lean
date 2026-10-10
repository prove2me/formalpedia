-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepSum.finrank_sup_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:20:01.509986+00:00
-- url     : https://prove2.me/submissions/2f0d450d-4582-4bed-ad17-61c2c1237d47

-- Generated from ChapterLorentzRealRepSum.lean — solution of BookProof.ChapterLorentzRealRepSum.finrank_sup_eq_add
import Mathlib
import Definitions.Def_ChapterLorentzRealRepSum
import Theorems.Thm_BookProof_ChapterLorentzRealRepSum_finrank_WHalf
import Theorems.Thm_BookProof_ChapterLorentzRealRepSum_finrank_W10
import Theorems.Thm_BookProof_ChapterLorentzRealRepSum_finrank_WPs
import Theorems.Thm_BookProof_ChapterLorentzRealRepSum_finrank_sup
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open Module

set_option maxHeartbeats 1000000 in
theorem solution :
    finrank ℝ ↥(WHalf ⊔ W10 ⊔ WPs) = finrank ℝ WHalf + finrank ℝ W10 + finrank ℝ WPs := by

  rw [finrank_sup, finrank_WHalf, finrank_W10, finrank_WPs]
