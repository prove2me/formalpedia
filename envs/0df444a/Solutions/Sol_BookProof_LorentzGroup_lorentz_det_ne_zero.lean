-- Prove2me | solution 1 for BookProof.LorentzGroup.lorentz_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:42:57.696977+00:00
-- url     : https://prove2.me/submissions/19df032e-66c3-44ba-9d5f-9872335de7ab

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.lorentz_det_ne_zero
import Mathlib
import Definitions.Def_ChapterLorentzGroup
import Theorems.Thm_BookProof_LorentzGroup_lorentz_det_sq_one
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    l.det ≠ 0 := by

      have := lorentz_det_sq_one h; aesop;
