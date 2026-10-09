-- Prove2me | solution 1 for BookProof.ChapterA3.adRot_mem_lorentzLie
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:06:30.62658+00:00
-- url     : https://prove2.me/submissions/56de454c-721c-43f5-b702-d687d35ffce4

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.adRot_mem_lorentzLie
import Mathlib
import Definitions.Def_ChapterA3e
import Theorems.Thm_BookProof_ChapterA3_lorentzLie_of_intModel
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) : adRot j ∈ LorentzLie := by

  have h : adRotZ j * minkowskiMatZ + minkowskiMatZ * (adRotZ j)ᵀ = 0 := by
    fin_cases j <;> decide
  exact lorentzLie_of_intModel (adRotZ j) h
