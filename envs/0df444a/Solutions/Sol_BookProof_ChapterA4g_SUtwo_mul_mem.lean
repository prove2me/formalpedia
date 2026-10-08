-- Prove2me | solution 1 for BookProof.ChapterA4g.SUtwo_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:43:27.500908+00:00
-- url     : https://prove2.me/submissions/0e6410cb-e6d2-4763-aac7-09a5cb69532d

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.SUtwo_mul_mem
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4c
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 4000000 in
theorem solution {S T : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ SUtwo) (hT : T ∈ SUtwo) : S * T ∈ SUtwo := by
  change (S * T).det = 1 ∧ (S * T)ᴴ * (S * T) = 1
  constructor
  · rw [Matrix.det_mul, hS.1, hT.1, one_mul]
  · rw [Matrix.conjTranspose_mul]
    calc
      Tᴴ * Sᴴ * (S * T) = Tᴴ * (Sᴴ * S) * T := by simp only [mul_assoc]
      _ = 1 := by rw [hS.2, mul_one, hT.2]

#print axioms solution

