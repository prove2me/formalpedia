-- Prove2me | solution 1 for BookProof.SmHiggsVacuum.higgsV_sq_form
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:19.834631+00:00
-- url     : https://prove2.me/submissions/97ed5544-6ba5-407f-b14b-bf30362c39ab

-- Generated from ChapterSmHiggsVacuum.lean — solution of BookProof.SmHiggsVacuum.higgsV_sq_form
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
open BookProof.SmHiggsVacuum




open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) :
    higgsV lam mu2 phi = (lam / 4) * (‖phi‖ ^ 2 - mu2 / lam) ^ 2 - mu2 ^ 2 / (4 * lam) := by

  have hne : lam ≠ 0 := ne_of_gt hlam
  rw [higgsV]
  field_simp
  ring
