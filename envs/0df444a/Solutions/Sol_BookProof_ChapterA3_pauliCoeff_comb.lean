-- Prove2me | solution 1 for BookProof.ChapterA3.pauliCoeff_comb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:26:31.426527+00:00
-- url     : https://prove2.me/submissions/86e9946b-1a92-46b1-8109-6e84a35ff56a

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.pauliCoeff_comb
import Mathlib
import Definitions.Def_ChapterA3h
import Theorems.Thm_BookProof_ChapterA3_paulisigma_trace
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin 4 → ℂ) (μ : Fin 4) :
    pauliCoeff (∑ ν, c ν • pauliσ ν) μ = c μ := by

  unfold pauliCoeff;
  simp [ Matrix.mul_sum, Matrix.trace_sum, paulisigma_trace ];
  ring
