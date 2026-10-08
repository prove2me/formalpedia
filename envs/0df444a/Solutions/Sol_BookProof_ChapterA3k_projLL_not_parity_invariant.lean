-- Prove2me | solution 1 for BookProof.ChapterA3k.projLL_not_parity_invariant
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:29:38.088141+00:00
-- url     : https://prove2.me/submissions/796084fa-86e0-4238-bb30-54aca1a947d0

import Mathlib
import Definitions.Def_ChapterA3k
open Matrix
open scoped Kronecker
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k


theorem solution : parityDiag * projLL ≠ projLL * parityDiag := by
  intro h
  simp only [parityDiag, projLL, ← Matrix.mul_kronecker_mul] at h
  have he := congrArg (fun M : M2 => M (0, 0) (2, 3)) h
  norm_num [Matrix.kronecker_apply, Matrix.mul_apply, projChirL,
    Matrix.smul_apply, mgamma, mgammaZ, chir, mgamma5, mgamma5Z,
    Fin.sum_univ_succ, Matrix.one_apply, Fin.reduceFinMk] at he
  simp at he
  have hi := congrArg Complex.im he
  norm_num at hi

#print axioms solution
