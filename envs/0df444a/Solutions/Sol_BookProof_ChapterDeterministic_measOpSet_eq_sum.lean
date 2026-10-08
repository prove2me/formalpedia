-- Prove2me | solution 1 for BookProof.ChapterDeterministic.measOpSet_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:49:16.063318+00:00
-- url     : https://prove2.me/submissions/c370b3ac-948c-4802-9608-a548120defea

-- Generated from ChapterDeterministic.lean — solution of BookProof.ChapterDeterministic.measOpSet_eq_sum
import Mathlib
import Definitions.Def_ChapterDeterministic
open BookProof.ChapterDeterministic



open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct BookProof.ChapterTimeTranslation


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix (Fin n) (Fin n) ℂ) (B : Finset (Fin n)) :
    measOpSet U B = ∑ b ∈ B, measOp U b := by

  unfold measOpSet measOp;    simp only [mul_assoc] ;
  unfold projSet; simp [ Finset.sum_mul, Finset.mul_sum ] ;
