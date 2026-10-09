-- Prove2me | solution 1 for BookProof.ChapterF3.diagGen_eigenstate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:00:12.669745+00:00
-- url     : https://prove2.me/submissions/9f44f91e-11ee-4de6-96d3-e4f107d8bae8

-- Generated from ChapterF3.lean — solution of BookProof.ChapterF3.diagGen_eigenstate
import Mathlib
import Definitions.Def_ChapterF3
import Theorems.Thm_BookProof_ChapterF1_numberOp_monomial
import Definitions.Def_ChapterF1
open BookProof
open BookProof.ChapterF1
open BookProof.ChapterF3



open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (a : ℂ) (n : ℕ) :
    (a • ChapterF1.numberOp) (X ^ n) = (a * n) • X ^ n := by

  convert congr_arg (fun x => a • x) (ChapterF1.numberOp_monomial n) using 1
    <;> (first | norm_num [mul_assoc, smul_smul] | simp only [mul_smul])
