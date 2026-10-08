-- Prove2me | solution 1 for BookProof.ChapterA4g.SEtwo_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:43:29.4513+00:00
-- url     : https://prove2.me/submissions/643bf66d-fb05-4328-8835-e1a0b9cc912b

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.SEtwo_mul_mem
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4d
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 4000000 in
theorem solution {S T : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ SEtwo) (hT : T ∈ SEtwo) : S * T ∈ SEtwo := by
  change (S * T).det = 1 ∧ (S * T) 0 1 = 0 ∧ Complex.normSq ((S * T) 0 0) = 1
  rcases hS with ⟨hSd, hSz, hSn⟩
  rcases hT with ⟨hTd, hTz, hTn⟩
  refine ⟨by rw [Matrix.det_mul, hSd, hTd, one_mul], ?_, ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hSz, hTz]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hSz, Complex.normSq_mul, hSn, hTn]

#print axioms solution

