-- Prove2me | solution 1 for BookProof.ChapterA3.adBoost_mem_lorentzLie
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:06:18.248816+00:00
-- url     : https://prove2.me/submissions/a68bac9c-7998-4d2c-9d9c-19bfce854f2e

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.adBoost_mem_lorentzLie
import Mathlib
import Definitions.Def_ChapterA3e
import Theorems.Thm_BookProof_ChapterA3_lorentzLie_of_intModel
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) : adBoost j ∈ LorentzLie := by

  have h : adBoostZ j * minkowskiMatZ + minkowskiMatZ * (adBoostZ j)ᵀ = 0 := by
    fin_cases j <;> decide
  exact lorentzLie_of_intModel (adBoostZ j) h
