-- Prove2me | solution 1 for BookProof.ChapterA4g.SUtwo_conjTranspose_mem
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:45:30.260774+00:00
-- url     : https://prove2.me/submissions/f7745038-2a60-41c4-a617-5a9395cc9a5b

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.SUtwo_conjTranspose_mem
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4c
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 4000000 in
theorem solution {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ SUtwo) : Sᴴ ∈ SUtwo := by
  change Sᴴ.det = 1 ∧ Sᴴᴴ * Sᴴ = 1
  constructor
  · rw [Matrix.det_conjTranspose, hS.1]
    simp
  · rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hS.2

#print axioms solution
