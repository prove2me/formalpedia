-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.exists_boost_null
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:27.519214+00:00
-- url     : https://prove2.me/submissions/5e677fbb-ba6a-474e-9b0f-ec9fd7a93add

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.exists_boost_null
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_nullMom
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin 4 → ℝ) (hp0 : 0 < p 0)
    (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ act A (hermOfMom nullMom) = hermOfMom p := by

  have hs : ((p 0 : ℂ)) ^ 2 - (p 1 : ℂ) ^ 2 - (p 2 : ℂ) ^ 2 - (p 3 : ℂ) ^ 2 = 0 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hshell
  have hconj2 : (starRingEnd ℂ) 2 = 2 := by
    rw [show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [hermOfMom_nullMom]
  by_cases hpp : 0 < p 0 + p 3
  · -- generic case: the first column of `A` is the square root of the null direction
    set t : ℝ := Real.sqrt ((p 0 + p 3) / 2) with ht
    have ht2 : t ^ 2 = (p 0 + p 3) / 2 := Real.sq_sqrt (by positivity)
    have ht2C : (t : ℂ) ^ 2 = ((p 0 : ℂ) + (p 3 : ℂ)) / 2 := by
      have h := congrArg (fun x : ℝ => (x : ℂ)) ht2
      push_cast at h; exact h
    have htpos : 0 < t := Real.sqrt_pos.mpr (by positivity)
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt htpos
    refine ⟨!![(t : ℂ), 0; ((p 1 : ℂ) + I * (p 2 : ℂ)) / (2 * t), (1 / t : ℂ)], ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      field_simp
      ring
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [act, hermOfMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
        field_simp
      · linear_combination 2 * ht2C
      · rw [hconj2]; ring
      · rw [hconj2]
        linear_combination -hs - (p 2 : ℂ) ^ 2 * Complex.I_sq
          - 2 * ((p 0 : ℂ) - (p 3 : ℂ)) * ht2C
  · -- degenerate case `p⁰ + p³ = 0`: then `p⃗` points along `-z` and `p¹ = p² = 0`
    push_neg at hpp
    have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2)]
    have h2 : p 2 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2)]
    have h3 : p 3 = -p 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2)]
    set w : ℝ := Real.sqrt (p 0) with hw
    have hw2 : w ^ 2 = p 0 := Real.sq_sqrt (le_of_lt hp0)
    have hw2C : (w : ℂ) ^ 2 = (p 0 : ℂ) := by
      have h := congrArg (fun x : ℝ => (x : ℂ)) hw2
      push_cast at h; exact h
    have hwpos : 0 < w := Real.sqrt_pos.mpr hp0
    have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hwpos
    refine ⟨!![0, -(1 / w : ℂ); (w : ℂ), 0], ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      field_simp
      norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [act, hermOfMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          h1, h2, h3]
      all_goals linear_combination 2 * hw2C
