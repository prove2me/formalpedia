-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qjC_eq_dirac
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:26.00931+00:00
-- url     : https://prove2.me/submissions/db2defd1-2979-463e-bc45-1f35f789c1cf

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qjC_eq_dirac
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : dgamma 0 * ((-Complex.I) • mgamma5) = qjC := by

  rw [dgamma, qjC, Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul_neg,
    Complex.I_mul_I, neg_one_smul]
