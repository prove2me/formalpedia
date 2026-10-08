-- Prove2me | solution 1 for BookProof.ChapterA3k.projLL_ne_projRR
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:29:35.606986+00:00
-- url     : https://prove2.me/submissions/37c32403-621d-4f9c-9336-914aa7eeb573

import Mathlib
import Definitions.Def_ChapterA3k
open Matrix
open scoped Kronecker
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k


theorem solution : projLL ≠ projRR := by
  intro h
  have he := congrArg (fun M : M2 => M (0, 0) (0, 1)) h
  norm_num [projLL, projRR, Matrix.kronecker_apply, projChirL, projChirR,
    Matrix.smul_apply, chir, mgamma5, mgamma5Z] at he
  have hi := congrArg Complex.im he
  norm_num at hi

#print axioms solution
