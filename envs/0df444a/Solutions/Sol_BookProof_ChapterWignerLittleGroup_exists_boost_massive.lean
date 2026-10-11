-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.exists_boost_massive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:26.123852+00:00
-- url     : https://prove2.me/submissions/24662d7e-f084-4476-98e2-5ae8b1eaa647

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.exists_boost_massive
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_sq_two
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_restMom
open BookProof.ChapterWignerLittleGroup



open Matrix Complex


@[simp] private theorem hermOfMom_conjTranspose (p : Fin 4 → ℝ) :
    (hermOfMom p)ᴴ = hermOfMom p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfMom, Matrix.conjTranspose_apply, Complex.ext_iff]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ) (hp0 : 0 < p 0)
    (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = m ^ 2) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      act A (hermOfMom (restMom m)) = hermOfMom p := by

  have hs : ((p 0 : ℂ)) ^ 2 - (p 1 : ℂ) ^ 2 - (p 2 : ℂ) ^ 2 - (p 3 : ℂ) ^ 2 = (m : ℂ) ^ 2 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hshell
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hpm : ((p 0 : ℂ) + (m : ℂ)) ≠ 0 := by
    have h : ((p 0 + m : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (by linarith : (0:ℝ) < p 0 + m)
    push_cast at h; exact h
  rw [hermOfMom_restMom]
  set M : Matrix (Fin 2) (Fin 2) ℂ := hermOfMom p + (m : ℂ) • 1 with hM
  have hMdet : M.det = ((2 * m * (p 0 + m) : ℝ) : ℂ) := by
    simp [hM, hermOfMom, Matrix.det_fin_two]
    linear_combination hs + (p 2 : ℂ) ^ 2 * Complex.I_sq
  have hMtr : M.trace = ((2 * (p 0 + m) : ℝ) : ℂ) := by
    simp [hM, hermOfMom, Matrix.trace_fin_two]
    ring
  have hMherm : Mᴴ = M := by
    simp [hM, Matrix.conjTranspose_add, hermOfMom_conjTranspose, Matrix.conjTranspose_smul]
  set c : ℝ := Real.sqrt (1 / (2 * (p 0 + m) * m)) with hc
  have hc2 : c ^ 2 = 1 / (2 * (p 0 + m) * m) := Real.sq_sqrt (by positivity)
  have hcC : ((c : ℂ)) * (c : ℂ) = ((1 / (2 * (p 0 + m) * m) : ℝ) : ℂ) := by
    rw [← hc2]; push_cast; ring
  have hMM : M * M = ((2 * (p 0 + m) : ℝ) : ℂ) • hermOfMom p := by
    rw [sq_two, hMtr, hMdet, hM, smul_add, smul_smul]
    push_cast
    module
  have hscal : ((c : ℂ) * (c : ℂ) * (m : ℂ)) * ((2 * (p 0 + m) : ℝ) : ℂ) = 1 := by
    rw [hcC]; push_cast; field_simp
  refine ⟨(c : ℂ) • M, ?_, ?_⟩
  · rw [Matrix.det_smul, hMdet]
    simp only [Fintype.card_fin, pow_two]
    rw [hcC]
    push_cast
    field_simp
  · simp only [act, Matrix.conjTranspose_smul, hMherm, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hMM]
    refine Eq.trans ?_ (one_smul ℂ (hermOfMom p))
    congr 1
    linear_combination hscal
