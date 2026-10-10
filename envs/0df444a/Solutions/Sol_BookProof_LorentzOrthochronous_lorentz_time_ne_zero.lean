-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.lorentz_time_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:51:48.37254+00:00
-- url     : https://prove2.me/submissions/74ca0dc3-caa3-47c7-bc9c-f83835ca0b3b

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.lorentz_time_ne_zero
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_time_sq_ge_one
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    l 0 0 ≠ 0 := by

  have := lorentz_time_sq_ge_one h
  intro hc; rw [hc] at this; norm_num at this
