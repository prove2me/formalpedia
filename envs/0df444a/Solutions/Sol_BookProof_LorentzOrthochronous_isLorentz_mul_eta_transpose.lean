-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.isLorentz_mul_eta_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:46:44.843016+00:00
-- url     : https://prove2.me/submissions/92ff297f-e487-4772-85ca-fc003ee8ff8f

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.isLorentz_mul_eta_transpose
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_inv_eq
import Theorems.Thm_BookProof_LorentzGroup_eta_mul_self
import Theorems.Thm_BookProof_LorentzGroup_lorentz_det_ne_zero
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    l * eta * lᵀ = eta := by

  have hinv : l⁻¹ = eta * lᵀ * eta := lorentz_inv_eq h
  have hunit : IsUnit l.det := isUnit_iff_ne_zero.mpr (lorentz_det_ne_zero h)
  have hmul : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hunit
  rw [hinv] at hmul
  have : (l * eta * lᵀ) * eta = 1 := by rw [← hmul]; simp [Matrix.mul_assoc]
  have h2 := congr_arg (· * eta) this
  simp only [Matrix.one_mul, Matrix.mul_assoc, eta_mul_self, Matrix.mul_one] at h2
  simpa [Matrix.mul_assoc] using h2
