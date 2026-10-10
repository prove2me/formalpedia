-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.isLorentz_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:46:15.162828+00:00
-- url     : https://prove2.me/submissions/a5ccae6b-0ce3-40cc-925d-b5a113ce8d42

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.isLorentz_neg
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    IsLorentz (-l) := by

  unfold IsLorentz at *
  simp only [transpose_neg, neg_mul, mul_neg, neg_neg]
  exact h
