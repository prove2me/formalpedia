-- Prove2me | solution 1 for BookProof.ChapterUniformPrior.eq_of_isRelabelingInvariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:57:10.522009+00:00
-- url     : https://prove2.me/submissions/28150be4-9165-4ab2-9b5d-c5686a1817b8

-- Generated from ChapterUniformPrior.lean — solution of BookProof.ChapterUniformPrior.eq_of_isRelabelingInvariant
import Mathlib
import Definitions.Def_ChapterUniformPrior
open BookProof.ChapterUniformPrior



open scoped BigOperators


variable {Hyp Data : Type*}

variable {Hyp Data : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (p : Hyp → ℝ)
    (hp : IsRelabelingInvariant p) (a b : Hyp) : p a = p b := by

  classical
  have h := congr_fun (hp (Equiv.swap a b)) b
  simpa [Function.comp_apply] using h
