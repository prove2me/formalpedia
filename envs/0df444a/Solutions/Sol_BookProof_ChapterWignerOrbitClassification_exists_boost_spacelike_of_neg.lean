-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:53:07.032145+00:00
-- url     : https://prove2.me/submissions/033212ba-485c-45f6-a1f6-fe34b10cd0c1

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_neg
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_hermOfMom_spaceRefMom
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ)
    (hshell : minkSq p = -m ^ 2) (hneg : p 0 + p 3 < 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      act A (hermOfMom (spaceRefMom m)) = hermOfMom p := by

  have hs : ((p 0 : ℂ)) ^ 2 - (p 1 : ℂ) ^ 2 - (p 2 : ℂ) ^ 2 - (p 3 : ℂ) ^ 2 = -(m : ℂ) ^ 2 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hshell
    simp only [minkSq] at h
    push_cast at h
    exact h
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  rw [hermOfMom_spaceRefMom]
  have ha0 : (p 0 : ℂ) + (p 3 : ℂ) ≠ 0 := by
    have : ((p 0 + p 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_lt hneg
    push_cast at this
    exact this
  set s : ℝ := Real.sqrt (-(p 0 + p 3) / m) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.2 (by
    have h1 : 0 < -(p 0 + p 3) := by linarith
    positivity)
  have hs2 : s ^ 2 = -(p 0 + p 3) / m := Real.sq_sqrt (by
    have h1 : 0 < -(p 0 + p 3) := by linarith
    positivity)
  have hsa : (s : ℂ) ^ 2 * (m : ℂ) = -((p 0 : ℂ) + (p 3 : ℂ)) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hs2
    push_cast at h
    field_simp at h ⊢
    linear_combination h
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hspos
  refine ⟨!![0, (s : ℂ);
      (m : ℂ) * (s : ℂ) / ((p 0 : ℂ) + (p 3 : ℂ)),
      ((p 1 : ℂ) + I * (p 2 : ℂ)) * (s : ℂ) / ((p 0 : ℂ) + (p 3 : ℂ))], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination -hsa
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [act, hermOfMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Complex.conj_ofReal] <;>
      field_simp
    · linear_combination -hsa
    · linear_combination -((p 1 : ℂ) - I * (p 2 : ℂ)) * hsa
    · linear_combination -((p 1 : ℂ) + I * (p 2 : ℂ)) * hsa
    · linear_combination ((m : ℂ) ^ 2 - ((p 1 : ℂ) + I * (p 2 : ℂ)) * ((p 1 : ℂ) - I * (p 2 : ℂ)))
        * hsa - ((p 0 : ℂ) + (p 3 : ℂ)) * hs
        - ((p 0 : ℂ) + (p 3 : ℂ)) * (p 2 : ℂ) ^ 2 * Complex.I_sq
