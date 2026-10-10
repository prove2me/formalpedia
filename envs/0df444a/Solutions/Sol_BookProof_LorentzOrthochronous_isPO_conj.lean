-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.isPO_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:55:47.486932+00:00
-- url     : https://prove2.me/submissions/299e9cab-f800-419c-b9f7-ea2cd58b8149

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.isPO_conj
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Theorems.Thm_BookProof_LorentzOrthochronous_isLorentz_neg
import Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_inv_eq
import Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_time_ne_zero
import Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_inv_time
import Theorems.Thm_BookProof_LorentzOrthochronous_orthochronous_mul
import Theorems.Thm_BookProof_LorentzGroup_isLorentz_inv
import Theorems.Thm_BookProof_LorentzGroup_isLorentz_mul
import Theorems.Thm_BookProof_LorentzGroup_lorentz_det_ne_zero
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {g s : Matrix (Fin 4) (Fin 4) ℝ}
    (hg : IsLorentz g) (hs : IsProperOrthochronous s) :
    IsProperOrthochronous (g * s * g⁻¹) := by

  obtain ⟨hsL, hsd, hs0⟩ := hs
  have hgunit : IsUnit g.det := isUnit_iff_ne_zero.mpr (lorentz_det_ne_zero hg)
  have hginvL : IsLorentz g⁻¹ := isLorentz_inv hg
  have hL : IsLorentz (g * s * g⁻¹) := isLorentz_mul (isLorentz_mul hg hsL) hginvL
  refine ⟨hL, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hsd, Matrix.det_nonsing_inv, mul_one,
      Ring.mul_inverse_cancel _ hgunit]
  · have hg0 := lorentz_time_ne_zero hg
    rcases lt_or_gt_of_ne hg0 with hneg | hpos
    · -- `g⁰₀ < 0`: conjugate by `-g` instead (the two sign flips cancel)
      have hng : IsLorentz (-g) := isLorentz_neg hg
      have hng0 : 0 < (-g) 0 0 := by rw [neg_apply]; linarith
      have hnginvL : IsLorentz (-g)⁻¹ := isLorentz_inv hng
      have hnginv0 : 0 < (-g)⁻¹ 0 0 := by rw [lorentz_inv_time hng, neg_apply]; linarith
      have h1 : 0 < ((-g) * s) 0 0 := orthochronous_mul hng hsL hng0 hs0
      have key : 0 < ((-g) * s * (-g)⁻¹) 0 0 :=
        orthochronous_mul (isLorentz_mul hng hsL) hnginvL h1 hnginv0
      have hneginv : (-g)⁻¹ = -(g⁻¹) := by
        rw [lorentz_inv_eq hng, lorentz_inv_eq hg, transpose_neg]
        simp 
      have heq : (-g) * s * (-g)⁻¹ = g * s * g⁻¹ := by
        rw [hneginv]; simp 
      rw [heq] at key; exact key
    · -- `g⁰₀ > 0`: both `g` and `g⁻¹` are orthochronous
      have hginv0 : 0 < g⁻¹ 0 0 := by rw [lorentz_inv_time hg]; exact hpos
      have h1 : 0 < (g * s) 0 0 := orthochronous_mul hg hsL hpos hs0
      exact orthochronous_mul (isLorentz_mul hg hsL) hginvL h1 hginv0
