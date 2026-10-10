-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.isPO_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:55:38.464916+00:00
-- url     : https://prove2.me/submissions/32798721-a79a-42c7-a539-856f52cc40a6

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.isPO_mul
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Theorems.Thm_BookProof_LorentzOrthochronous_orthochronous_mul
import Theorems.Thm_BookProof_LorentzGroup_isLorentz_mul
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {a b : Matrix (Fin 4) (Fin 4) ℝ}
    (ha : IsProperOrthochronous a) (hb : IsProperOrthochronous b) :
    IsProperOrthochronous (a * b) := by

  obtain ⟨haL, had, ha0⟩ := ha
  obtain ⟨hbL, hbd, hb0⟩ := hb
  exact ⟨isLorentz_mul haL hbL, by rw [Matrix.det_mul, had, hbd]; ring,
    orthochronous_mul haL hbL ha0 hb0⟩
