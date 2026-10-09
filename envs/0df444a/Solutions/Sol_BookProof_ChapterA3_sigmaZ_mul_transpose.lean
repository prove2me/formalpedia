-- Prove2me | solution 1 for BookProof.ChapterA3.sigmaZ_mul_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:34:17.557245+00:00
-- url     : https://prove2.me/submissions/91963083-7ba2-4093-a163-7a1a38e76a7b

-- Generated from ChapterA3i.lean — solution of BookProof.ChapterA3.sigmaZ_mul_transpose
import Mathlib
import Definitions.Def_ChapterA3i
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution :
    SigmaZ * SigmaZᵀ = (2 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by

  decide
