-- Prove2me | solution 1 for BookProof.ChapterParityHiggs.realityOp_realityOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:53.651985+00:00
-- url     : https://prove2.me/submissions/aca04d80-62f2-4675-a1eb-857d3c078875

-- Generated from ChapterParityHiggs.lean — solution of BookProof.ChapterParityHiggs.realityOp_realityOp
import Mathlib
import Definitions.Def_ChapterParityHiggs
import Definitions.Def_ChapterParity
open BookProof.ChapterParityHiggs



open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (v : I → ℂ) :
    realityOp M (realityOp M v) = (M * M.map (starRingEnd ℂ)) *ᵥ v := by

  rw [← Matrix.mulVec_mulVec]
  unfold realityOp
  congr 1
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Complex.conj_conj]
