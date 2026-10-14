-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:53:07.996299+00:00
-- url     : https://prove2.me/submissions/44068c42-7f51-4eb6-a000-fc8e089e03e2

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_zero
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
    (hshell : minkSq p = -m ^ 2) (hzero : p 0 + p 3 = 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      act A (hermOfMom (spaceRefMom m)) = hermOfMom p := by

  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hp3 : p 3 = -p 0 := by linarith
  have hshell' : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = -m ^ 2 := hshell
  have hnorm : p 1 ^ 2 + p 2 ^ 2 = m ^ 2 := by
    rw [hp3] at hshell'; nlinarith [hshell']
  rw [hermOfMom_spaceRefMom]
  obtain ⟨beta, hbeta⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-(((p 1 : ℂ) - I * (p 2 : ℂ)) / (m : ℂ))) (n := 2) two_pos
  have hnsb : Complex.normSq ((p 1 : ℂ) - I * (p 2 : ℂ)) = p 1 ^ 2 + p 2 ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  have hns : Complex.normSq beta = 1 := by
    have h1 : Complex.normSq (beta ^ 2) = Complex.normSq beta * Complex.normSq beta := by
      rw [pow_two, Complex.normSq_mul]
    rw [hbeta] at h1
    have h2 : Complex.normSq (-(((p 1 : ℂ) - I * (p 2 : ℂ)) / (m : ℂ))) = 1 := by
      rw [Complex.normSq_neg, Complex.normSq_div, hnsb]
      have hmm : Complex.normSq ((m : ℝ) : ℂ) = m ^ 2 := by
        simp [Complex.normSq_apply]; ring
      rw [hmm, hnorm]
      field_simp
    rw [h2] at h1
    nlinarith [Complex.normSq_nonneg beta, h1]
  have hbb : beta * (starRingEnd ℂ) beta = 1 := by
    rw [Complex.mul_conj, hns]
    norm_num
  have hbeta' : beta ^ 2 * (m : ℂ) = -((p 1 : ℂ) - I * (p 2 : ℂ)) := by
    rw [hbeta]; field_simp
  have hbetac' : (starRingEnd ℂ) beta ^ 2 * (m : ℂ) = -((p 1 : ℂ) + I * (p 2 : ℂ)) := by
    have h := congrArg (starRingEnd ℂ) hbeta'
    simpa [map_mul, map_pow, Complex.conj_ofReal, sub_eq_add_neg] using h
  set lam : ℝ := -(m + 2 * p 0) / (2 * m) with hlam
  have hlamC : (lam : ℂ) * (2 * (m : ℂ)) = -((m : ℂ) + 2 * (p 0 : ℂ)) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hlam
    push_cast at h
    rw [h]
    field_simp
  refine ⟨!![beta, beta;
      (lam : ℂ) * (starRingEnd ℂ) beta, ((lam : ℂ) + 1) * (starRingEnd ℂ) beta], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hbb
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [act, hermOfMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Complex.conj_ofReal, hp3] <;>
      field_simp
    · linear_combination -hbeta'
    · linear_combination -hbetac'
    · linear_combination (-(m : ℂ) * (2 * (lam : ℂ) + 1)) * hbb - hlamC
