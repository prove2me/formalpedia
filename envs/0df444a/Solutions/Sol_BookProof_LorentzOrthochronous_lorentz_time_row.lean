-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.lorentz_time_row
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:49:16.173087+00:00
-- url     : https://prove2.me/submissions/40513bf1-44c3-4923-a7b5-baaa7448f2c9

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.lorentz_time_row
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Theorems.Thm_BookProof_LorentzOrthochronous_isLorentz_mul_eta_transpose
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    (l 0 0) ^ 2 = 1 + (l 0 1) ^ 2 + (l 0 2) ^ 2 + (l 0 3) ^ 2 := by

  have hd := isLorentz_mul_eta_transpose h
  have h00 := congr_fun (congr_fun hd 0) 0
  simp [mul_apply, Fin.sum_univ_four, eta] at h00
  ring_nf at h00 ⊢
  linarith [h00]
