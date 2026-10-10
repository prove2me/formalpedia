-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.lorentz_inv_time
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:53:01.139834+00:00
-- url     : https://prove2.me/submissions/02709942-eeb4-4322-9908-aa79e507bb6d

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.lorentz_inv_time
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_inv_eq
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    l⁻¹ 0 0 = l 0 0 := by

  rw [lorentz_inv_eq h]
  simp [mul_apply, Fin.sum_univ_four, eta, vecMul, dotProduct]
