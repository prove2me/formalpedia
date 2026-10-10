-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.isPO_inv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:55:42.777821+00:00
-- url     : https://prove2.me/submissions/a8bbfbeb-9d48-46f4-a39d-9544870eedb8

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.isPO_inv
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_inv_time
import Theorems.Thm_BookProof_LorentzGroup_isLorentz_inv
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsProperOrthochronous l) :
    IsProperOrthochronous l⁻¹ := by

  obtain ⟨hL, hd, h0⟩ := h
  refine ⟨isLorentz_inv hL, ?_, ?_⟩
  · rw [Matrix.det_nonsing_inv, hd]; simp
  · rw [lorentz_inv_time hL]; exact h0
