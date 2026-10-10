-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.lorentz_time_sq_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:50:26.188815+00:00
-- url     : https://prove2.me/submissions/0ac5b1ed-97cc-4647-a778-9932f6f89719

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.lorentz_time_sq_ge_one
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_time_col
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    1 ≤ (l 0 0) ^ 2 := by

  have := lorentz_time_col h
  nlinarith [sq_nonneg (l 1 0), sq_nonneg (l 2 0), sq_nonneg (l 3 0)]
