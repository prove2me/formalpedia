-- Prove2me | solution 1 for BookProof.SmHiggsVacuum.higgsV_eq_min_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:21.674105+00:00
-- url     : https://prove2.me/submissions/e9def5a3-5c60-4331-87f4-e65669ff7a3d

-- Generated from ChapterSmHiggsVacuum.lean — solution of BookProof.SmHiggsVacuum.higgsV_eq_min_iff
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
import Theorems.Thm_BookProof_SmHiggsVacuum_higgsV_sq_form
open BookProof.SmHiggsVacuum




open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) :
    higgsV lam mu2 phi = -(mu2 ^ 2 / (4 * lam)) ↔ ‖phi‖ ^ 2 = mu2 / lam := by

  rw [higgsV_sq_form hlam]
  constructor
  · intro h
    have hz : (lam / 4) * (‖phi‖ ^ 2 - mu2 / lam) ^ 2 = 0 := by linarith
    have h4 : (lam / 4) ≠ 0 := by positivity
    have : (‖phi‖ ^ 2 - mu2 / lam) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' h4
      · exact h'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · intro h
    rw [h]
    simp
