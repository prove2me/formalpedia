-- Prove2me | solution 1 for BookProof.ChapterConservative.timeEvo_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:06:44.602005+00:00
-- url     : https://prove2.me/submissions/597a0ad4-24bd-48ce-b48f-ba513ca47043

-- Generated from ChapterConservative.lean — solution of BookProof.ChapterConservative.timeEvo_unitary
import Mathlib
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative



open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (timeEvo H t)ᴴ * (timeEvo H t) = 1 := by

  have hU : timeEvo H t = NormedSpace.exp ((t : ℂ) • (Complex.I • H)) := rfl
  -- Since `H` is Hermitian, `((t:ℂ) • (I • H))ᴴ = -(t:ℂ) • (I • H)`.
  have h_conj : ((t : ℂ) • (Complex.I • H))ᴴ = -(t : ℂ) • (Complex.I • H) := by
    simp only [Matrix.IsHermitian, Complex.coe_smul, Matrix.conjTranspose_smul, star_trivial,
        RCLike.star_def, Complex.conj_I, neg_smul, smul_neg, neg_inj] at hH ⊢
    rw [hH]
  rw [hU, ← Matrix.exp_conjTranspose]
  rw [h_conj, ← Matrix.exp_add_of_commute]
  · simp [NormedSpace.exp_zero]
  · simp [smul_smul]
