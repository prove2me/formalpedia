-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.lorentz_time_col
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:47:55.805578+00:00
-- url     : https://prove2.me/submissions/eff5b054-5685-4c5d-92a5-50c21b0ebced

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.lorentz_time_col
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    (l 0 0) ^ 2 = 1 + (l 1 0) ^ 2 + (l 2 0) ^ 2 + (l 3 0) ^ 2 := by

  have h00 := congr_fun (congr_fun h 0) 0
  simp [mul_apply, Fin.sum_univ_four, eta] at h00
  ring_nf at h00 ⊢
  linarith [h00]
