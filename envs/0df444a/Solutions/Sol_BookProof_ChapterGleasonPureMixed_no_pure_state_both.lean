-- Prove2me | solution 1 for BookProof.ChapterGleasonPureMixed.no_pure_state_both
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:47:40.774667+00:00
-- url     : https://prove2.me/submissions/70b3fdac-fd65-4d0d-a8da-1896fbc51bab

-- Generated from ChapterGleasonPureMixed.lean — solution of BookProof.ChapterGleasonPureMixed.no_pure_state_both
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterGleasonPureMixed



open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ ∃ ρ : Matrix (Fin 2) (Fin 2) ℝ, IsPureState ρ ∧ E ρ P0 = 1/2 ∧ E ρ Q = 1/2 := by

  rintro ⟨ρ, ⟨hsym, hidem, htr⟩, hP0, hQ⟩
  have e00 := congrFun (congrFun hidem 0) 0
  have esym := congrFun (congrFun hsym 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at e00 esym
  simp only [E, P0, Q, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.diag_apply] at hP0 hQ htr
  nlinarith [sq_nonneg (ρ 0 1), sq_nonneg (ρ 1 0), e00, esym, hP0, hQ, htr]
