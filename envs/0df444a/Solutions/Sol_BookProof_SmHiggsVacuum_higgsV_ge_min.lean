-- Prove2me | solution 1 for BookProof.SmHiggsVacuum.higgsV_ge_min
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:20.742615+00:00
-- url     : https://prove2.me/submissions/7b88a112-388a-4107-abd1-d2b4f24dc703

-- Generated from ChapterSmHiggsVacuum.lean — solution of BookProof.SmHiggsVacuum.higgsV_ge_min
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
    -(mu2 ^ 2 / (4 * lam)) ≤ higgsV lam mu2 phi := by

  rw [higgsV_sq_form hlam]
  have h : 0 ≤ (lam / 4) * (‖phi‖ ^ 2 - mu2 / lam) ^ 2 := by positivity
  linarith
